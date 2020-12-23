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
% DateTime   : Thu Dec  3 12:59:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 390 expanded)
%              Number of leaves         :   21 ( 105 expanded)
%              Depth                    :   19
%              Number of atoms          :  464 (2219 expanded)
%              Number of equality atoms :  209 (1057 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f329,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f214,f238,f277,f321,f328])).

fof(f328,plain,(
    ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f213,f302])).

fof(f302,plain,(
    sK3 != k2_mcart_1(sK4) ),
    inference(subsumption_resolution,[],[f301,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK3 = X7
                | k3_mcart_1(X5,X6,X7) != sK4
                | ~ m1_subset_1(X7,sK2) )
            | ~ m1_subset_1(X6,sK1) )
        | ~ m1_subset_1(X5,sK0) )
    & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f28])).

% (29895)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f28,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK3 = X7
                  | k3_mcart_1(X5,X6,X7) != sK4
                  | ~ m1_subset_1(X7,sK2) )
              | ~ m1_subset_1(X6,sK1) )
          | ~ m1_subset_1(X5,sK0) )
      & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

fof(f301,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f300,f41])).

% (29889)Refutation not found, incomplete strategy% (29889)------------------------------
% (29889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29889)Termination reason: Refutation not found, incomplete strategy

% (29889)Memory used [KB]: 10618
% (29889)Time elapsed: 0.139 s
% (29889)------------------------------
% (29889)------------------------------
% (29895)Refutation not found, incomplete strategy% (29895)------------------------------
% (29895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29895)Termination reason: Refutation not found, incomplete strategy

% (29895)Memory used [KB]: 1791
% (29895)Time elapsed: 0.139 s
% (29895)------------------------------
% (29895)------------------------------
% (29882)Refutation not found, incomplete strategy% (29882)------------------------------
% (29882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29882)Termination reason: Refutation not found, incomplete strategy

% (29882)Memory used [KB]: 10618
% (29882)Time elapsed: 0.134 s
% (29882)------------------------------
% (29882)------------------------------
% (29892)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (29881)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (29888)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (29892)Refutation not found, incomplete strategy% (29892)------------------------------
% (29892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29892)Termination reason: Refutation not found, incomplete strategy

% (29892)Memory used [KB]: 10746
% (29892)Time elapsed: 0.139 s
% (29892)------------------------------
% (29892)------------------------------
% (29890)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (29881)Refutation not found, incomplete strategy% (29881)------------------------------
% (29881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29881)Termination reason: Refutation not found, incomplete strategy

% (29881)Memory used [KB]: 10618
% (29881)Time elapsed: 0.139 s
% (29881)------------------------------
% (29881)------------------------------
% (29887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (29884)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (29880)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (29880)Refutation not found, incomplete strategy% (29880)------------------------------
% (29880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (29880)Termination reason: Refutation not found, incomplete strategy

% (29880)Memory used [KB]: 10746
% (29880)Time elapsed: 0.150 s
% (29880)------------------------------
% (29880)------------------------------
fof(f41,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f300,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f299,f42])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f299,plain,
    ( sK3 != k2_mcart_1(sK4)
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f298,f69])).

fof(f69,plain,(
    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f38,plain,(
    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f298,plain,
    ( sK3 != k2_mcart_1(sK4)
    | ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f43,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f60,f55])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
            & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
            & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
                & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3))
                & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

fof(f43,plain,(
    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f29])).

fof(f213,plain,
    ( sK3 = k2_mcart_1(sK4)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl7_10
  <=> sK3 = k2_mcart_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f321,plain,(
    ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f319,f40])).

fof(f319,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f318,f41])).

fof(f318,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f317,f42])).

fof(f317,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_9 ),
    inference(condensation,[],[f316])).

fof(f316,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f311,f89])).

fof(f89,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(resolution,[],[f87,f47])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5,X6] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK6(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
     => ( ! [X6,X5,X4,X3,X2] :
            ( r1_xboole_0(X2,X0)
            | ~ r2_hidden(X6,sK6(X0))
            | ~ r2_hidden(X5,X6)
            | ~ r2_hidden(X4,X5)
            | ~ r2_hidden(X3,X4)
            | ~ r2_hidden(X2,X3) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5,X6] :
              ( r1_xboole_0(X2,X0)
              | ~ r2_hidden(X6,X1)
              | ~ r2_hidden(X5,X6)
              | ~ r2_hidden(X4,X5)
              | ~ r2_hidden(X3,X4)
              | ~ r2_hidden(X2,X3) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f87,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1)) ),
    inference(resolution,[],[f86,f44])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f311,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_9 ),
    inference(superposition,[],[f77,f306])).

fof(f306,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_9 ),
    inference(resolution,[],[f292,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f47,f45])).

fof(f292,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_9 ),
    inference(resolution,[],[f286,f69])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) )
    | ~ spl7_9 ),
    inference(resolution,[],[f283,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f283,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))
    | ~ spl7_9 ),
    inference(resolution,[],[f209,f56])).

fof(f209,plain,
    ( ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl7_9
  <=> ! [X0] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f62,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f61,f55])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_xboole_0 != X3
          & k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3) )
      & ( k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3)
        | k1_xboole_0 = X3
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

fof(f277,plain,(
    ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f275,f40])).

fof(f275,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f274,f41])).

fof(f274,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f273,f42])).

fof(f273,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_8 ),
    inference(condensation,[],[f272])).

fof(f272,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f267,f89])).

fof(f267,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_8 ),
    inference(superposition,[],[f77,f262])).

fof(f262,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_8 ),
    inference(resolution,[],[f253,f83])).

fof(f253,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_8 ),
    inference(resolution,[],[f247,f69])).

fof(f247,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
        | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f244,f52])).

fof(f244,plain,
    ( ! [X0,X1] : ~ r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))
    | ~ spl7_8 ),
    inference(resolution,[],[f206,f56])).

fof(f206,plain,
    ( ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl7_8
  <=> ! [X1] : ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f238,plain,(
    ~ spl7_7 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f236,f40])).

fof(f236,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f235,f41])).

fof(f235,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f234,f42])).

fof(f234,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl7_7 ),
    inference(condensation,[],[f233])).

fof(f233,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f226,f89])).

fof(f226,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = sK2
        | k1_xboole_0 = sK1
        | k1_xboole_0 = sK0 )
    | ~ spl7_7 ),
    inference(superposition,[],[f77,f223])).

fof(f223,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f217,f83])).

fof(f217,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))
    | ~ spl7_7 ),
    inference(resolution,[],[f215,f69])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,k2_zfmisc_1(X0,sK2))
        | v1_xboole_0(k2_zfmisc_1(X0,sK2)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f203,f52])).

fof(f203,plain,
    ( ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl7_7
  <=> ! [X2] : ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f214,plain,
    ( spl7_7
    | spl7_8
    | spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f200,f211,f208,f205,f202])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( sK3 = k2_mcart_1(sK4)
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))
      | ~ r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))
      | ~ r2_hidden(sK4,k2_zfmisc_1(X2,sK2)) ) ),
    inference(equality_resolution,[],[f185])).

fof(f185,plain,(
    ! [X2,X0,X5,X1] :
      ( sK4 != X0
      | k2_mcart_1(X0) = sK3
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(condensation,[],[f183])).

fof(f183,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4))
      | ~ r2_hidden(X0,k2_zfmisc_1(X5,sK2)) ) ),
    inference(resolution,[],[f180,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f180,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK2)
      | k2_mcart_1(X0) = sK3
      | sK4 != X0
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1))
      | ~ r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2))
      | ~ r2_hidden(X0,k2_zfmisc_1(X3,X4)) ) ),
    inference(superposition,[],[f160,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f51,f50])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X1)
      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

fof(f160,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(X0,X1) != sK4
      | sK3 = X1
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,sK1))
      | ~ r2_hidden(X0,k2_zfmisc_1(sK0,X3)) ) ),
    inference(resolution,[],[f151,f56])).

fof(f151,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k1_mcart_1(X1),sK0)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,k2_zfmisc_1(X4,sK1)) ) ),
    inference(condensation,[],[f149])).

fof(f149,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | sK4 != k4_tarski(X1,X0)
      | ~ r2_hidden(k1_mcart_1(X1),sK0)
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,k2_zfmisc_1(X4,sK1)) ) ),
    inference(resolution,[],[f148,f57])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3))
      | k4_tarski(X0,X1) != sK4
      | ~ r2_hidden(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f147,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(k2_mcart_1(X1),sK1)
      | ~ r2_hidden(k1_mcart_1(X1),sK0) ) ),
    inference(resolution,[],[f146,f53])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k1_mcart_1(X1),sK0)
      | ~ m1_subset_1(X0,sK2)
      | sK4 != k4_tarski(X1,X0)
      | sK3 = X0
      | ~ r2_hidden(X1,k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(k2_mcart_1(X1),sK1) ) ),
    inference(resolution,[],[f137,f53])).

fof(f137,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k2_mcart_1(X0),sK1)
      | sK3 = X1
      | ~ m1_subset_1(X1,sK2)
      | k4_tarski(X0,X1) != sK4
      | ~ m1_subset_1(k1_mcart_1(X0),sK0)
      | ~ r2_hidden(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(superposition,[],[f68,f135])).

fof(f68,plain,(
    ! [X6,X7,X5] :
      ( sK4 != k4_tarski(k4_tarski(X5,X6),X7)
      | sK3 = X7
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(definition_unfolding,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f39,plain,(
    ! [X6,X7,X5] :
      ( sK3 = X7
      | k3_mcart_1(X5,X6,X7) != sK4
      | ~ m1_subset_1(X7,sK2)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f29])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 19:10:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (29894)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.49  % (29878)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.49  % (29886)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.50  % (29894)Refutation not found, incomplete strategy% (29894)------------------------------
% 0.20/0.50  % (29894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (29894)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (29894)Memory used [KB]: 10746
% 0.20/0.50  % (29894)Time elapsed: 0.056 s
% 0.20/0.50  % (29894)------------------------------
% 0.20/0.50  % (29894)------------------------------
% 0.20/0.52  % (29893)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.52  % (29876)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (29882)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (29893)Refutation not found, incomplete strategy% (29893)------------------------------
% 0.20/0.53  % (29893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (29871)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (29893)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (29893)Memory used [KB]: 1791
% 0.20/0.53  % (29893)Time elapsed: 0.111 s
% 0.20/0.53  % (29893)------------------------------
% 0.20/0.53  % (29893)------------------------------
% 0.20/0.53  % (29900)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (29885)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (29873)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (29875)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (29870)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (29870)Refutation not found, incomplete strategy% (29870)------------------------------
% 0.20/0.54  % (29870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29873)Refutation not found, incomplete strategy% (29873)------------------------------
% 0.20/0.54  % (29873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (29870)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  % (29873)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  
% 0.20/0.54  % (29870)Memory used [KB]: 1663
% 0.20/0.54  % (29873)Memory used [KB]: 10746
% 0.20/0.54  % (29870)Time elapsed: 0.125 s
% 0.20/0.54  % (29873)Time elapsed: 0.126 s
% 0.20/0.54  % (29870)------------------------------
% 0.20/0.54  % (29870)------------------------------
% 0.20/0.54  % (29873)------------------------------
% 0.20/0.54  % (29873)------------------------------
% 0.20/0.54  % (29896)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (29879)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (29899)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (29891)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (29897)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (29874)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (29901)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (29898)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (29883)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (29889)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (29874)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f329,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f214,f238,f277,f321,f328])).
% 0.20/0.55  fof(f328,plain,(
% 0.20/0.55    ~spl7_10),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f327])).
% 0.20/0.55  fof(f327,plain,(
% 0.20/0.55    $false | ~spl7_10),
% 0.20/0.55    inference(subsumption_resolution,[],[f213,f302])).
% 0.20/0.55  fof(f302,plain,(
% 0.20/0.55    sK3 != k2_mcart_1(sK4)),
% 0.20/0.55    inference(subsumption_resolution,[],[f301,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    k1_xboole_0 != sK0),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f28])).
% 0.20/0.55  % (29895)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (sK3 != k7_mcart_1(sK0,sK1,sK2,sK4) & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & ! [X5] : (! [X6] : (! [X7] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2)) | ~m1_subset_1(X6,sK1)) | ~m1_subset_1(X5,sK0)) & m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2)))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.55    inference(flattening,[],[f17])).
% 0.20/0.55  fof(f17,plain,(
% 0.20/0.55    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 0.20/0.55    inference(ennf_transformation,[],[f16])).
% 0.20/0.55  fof(f16,negated_conjecture,(
% 0.20/0.55    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.55    inference(negated_conjecture,[],[f15])).
% 0.20/0.55  fof(f15,conjecture,(
% 0.20/0.55    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).
% 0.20/0.55  fof(f301,plain,(
% 0.20/0.55    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK0),
% 0.20/0.55    inference(subsumption_resolution,[],[f300,f41])).
% 0.20/0.55  % (29889)Refutation not found, incomplete strategy% (29889)------------------------------
% 0.20/0.55  % (29889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29889)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29889)Memory used [KB]: 10618
% 0.20/0.55  % (29889)Time elapsed: 0.139 s
% 0.20/0.55  % (29889)------------------------------
% 0.20/0.55  % (29889)------------------------------
% 0.20/0.55  % (29895)Refutation not found, incomplete strategy% (29895)------------------------------
% 0.20/0.55  % (29895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29895)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29895)Memory used [KB]: 1791
% 0.20/0.55  % (29895)Time elapsed: 0.139 s
% 0.20/0.55  % (29895)------------------------------
% 0.20/0.55  % (29895)------------------------------
% 0.20/0.55  % (29882)Refutation not found, incomplete strategy% (29882)------------------------------
% 0.20/0.55  % (29882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29882)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29882)Memory used [KB]: 10618
% 0.20/0.55  % (29882)Time elapsed: 0.134 s
% 0.20/0.55  % (29882)------------------------------
% 0.20/0.55  % (29882)------------------------------
% 0.20/0.55  % (29892)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.55  % (29881)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (29888)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (29892)Refutation not found, incomplete strategy% (29892)------------------------------
% 0.20/0.55  % (29892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29892)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29892)Memory used [KB]: 10746
% 0.20/0.55  % (29892)Time elapsed: 0.139 s
% 0.20/0.55  % (29892)------------------------------
% 0.20/0.55  % (29892)------------------------------
% 0.20/0.55  % (29890)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.55  % (29881)Refutation not found, incomplete strategy% (29881)------------------------------
% 0.20/0.55  % (29881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (29881)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (29881)Memory used [KB]: 10618
% 0.20/0.55  % (29881)Time elapsed: 0.139 s
% 0.20/0.55  % (29881)------------------------------
% 0.20/0.55  % (29881)------------------------------
% 0.20/0.55  % (29887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.55  % (29884)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (29880)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.56  % (29880)Refutation not found, incomplete strategy% (29880)------------------------------
% 0.20/0.56  % (29880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (29880)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (29880)Memory used [KB]: 10746
% 0.20/0.56  % (29880)Time elapsed: 0.150 s
% 0.20/0.56  % (29880)------------------------------
% 0.20/0.56  % (29880)------------------------------
% 0.20/0.57  fof(f41,plain,(
% 0.20/0.57    k1_xboole_0 != sK1),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f300,plain,(
% 0.20/0.57    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(subsumption_resolution,[],[f299,f42])).
% 0.20/0.57  fof(f42,plain,(
% 0.20/0.57    k1_xboole_0 != sK2),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f299,plain,(
% 0.20/0.57    sK3 != k2_mcart_1(sK4) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(subsumption_resolution,[],[f298,f69])).
% 0.20/0.57  fof(f69,plain,(
% 0.20/0.57    m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2))),
% 0.20/0.57    inference(definition_unfolding,[],[f38,f55])).
% 0.20/0.57  fof(f55,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f8])).
% 0.20/0.57  fof(f8,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.57  fof(f38,plain,(
% 0.20/0.57    m1_subset_1(sK4,k3_zfmisc_1(sK0,sK1,sK2))),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f298,plain,(
% 0.20/0.57    sK3 != k2_mcart_1(sK4) | ~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 0.20/0.57    inference(superposition,[],[f43,f70])).
% 0.20/0.57  fof(f70,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f60,f55])).
% 0.20/0.57  fof(f60,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f27])).
% 0.20/0.57  fof(f27,plain,(
% 0.20/0.57    ! [X0,X1,X2] : (! [X3] : ((k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3))) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f12])).
% 0.20/0.57  fof(f12,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3) & k6_mcart_1(X0,X1,X2,X3) = k2_mcart_1(k1_mcart_1(X3)) & k5_mcart_1(X0,X1,X2,X3) = k1_mcart_1(k1_mcart_1(X3)))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).
% 0.20/0.57  fof(f43,plain,(
% 0.20/0.57    sK3 != k7_mcart_1(sK0,sK1,sK2,sK4)),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  fof(f213,plain,(
% 0.20/0.57    sK3 = k2_mcart_1(sK4) | ~spl7_10),
% 0.20/0.57    inference(avatar_component_clause,[],[f211])).
% 0.20/0.57  fof(f211,plain,(
% 0.20/0.57    spl7_10 <=> sK3 = k2_mcart_1(sK4)),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.57  fof(f321,plain,(
% 0.20/0.57    ~spl7_9),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f320])).
% 0.20/0.57  fof(f320,plain,(
% 0.20/0.57    $false | ~spl7_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f319,f40])).
% 0.20/0.57  fof(f319,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl7_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f318,f41])).
% 0.20/0.57  fof(f318,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f317,f42])).
% 0.20/0.57  fof(f317,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_9),
% 0.20/0.57    inference(condensation,[],[f316])).
% 0.20/0.57  fof(f316,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_9),
% 0.20/0.57    inference(subsumption_resolution,[],[f311,f89])).
% 0.20/0.57  fof(f89,plain,(
% 0.20/0.57    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.57    inference(resolution,[],[f87,f47])).
% 0.20/0.57  fof(f47,plain,(
% 0.20/0.57    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f35])).
% 0.20/0.57  fof(f35,plain,(
% 0.20/0.57    ! [X0] : ((! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK6(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f20,f34])).
% 0.20/0.57  fof(f34,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) => (! [X6,X5,X4,X3,X2] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,sK6(X0)) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(sK6(X0),X0)))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f20,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | ~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3)) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(flattening,[],[f19])).
% 0.20/0.57  fof(f19,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : (! [X2,X3,X4,X5,X6] : (r1_xboole_0(X2,X0) | (~r2_hidden(X6,X1) | ~r2_hidden(X5,X6) | ~r2_hidden(X4,X5) | ~r2_hidden(X3,X4) | ~r2_hidden(X2,X3))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.20/0.57    inference(ennf_transformation,[],[f14])).
% 0.20/0.57  fof(f14,axiom,(
% 0.20/0.57    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.57  fof(f87,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(k1_xboole_0,X1))) )),
% 0.20/0.57    inference(resolution,[],[f86,f44])).
% 0.20/0.57  fof(f44,plain,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    inference(cnf_transformation,[],[f2])).
% 0.20/0.57  fof(f2,axiom,(
% 0.20/0.57    v1_xboole_0(k1_xboole_0)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.57  fof(f86,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.57    inference(resolution,[],[f56,f45])).
% 0.20/0.57  fof(f45,plain,(
% 0.20/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f33])).
% 0.20/0.57  fof(f33,plain,(
% 0.20/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f31,f32])).
% 0.20/0.57  fof(f32,plain,(
% 0.20/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.20/0.57    introduced(choice_axiom,[])).
% 0.20/0.57  fof(f31,plain,(
% 0.20/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.57    inference(rectify,[],[f30])).
% 0.20/0.57  fof(f30,plain,(
% 0.20/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.57    inference(nnf_transformation,[],[f1])).
% 0.20/0.57  fof(f1,axiom,(
% 0.20/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.57  fof(f56,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f26,plain,(
% 0.20/0.57    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.20/0.57    inference(ennf_transformation,[],[f10])).
% 0.20/0.57  fof(f10,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.20/0.57  fof(f311,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_9),
% 0.20/0.57    inference(superposition,[],[f77,f306])).
% 0.20/0.57  fof(f306,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_9),
% 0.20/0.57    inference(resolution,[],[f292,f83])).
% 0.20/0.57  fof(f83,plain,(
% 0.20/0.57    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(resolution,[],[f47,f45])).
% 0.20/0.57  fof(f292,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_9),
% 0.20/0.57    inference(resolution,[],[f286,f69])).
% 0.20/0.57  fof(f286,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_9),
% 0.20/0.57    inference(resolution,[],[f283,f52])).
% 0.20/0.57  fof(f52,plain,(
% 0.20/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f24])).
% 0.20/0.57  fof(f24,plain,(
% 0.20/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.57    inference(flattening,[],[f23])).
% 0.20/0.57  fof(f23,plain,(
% 0.20/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f5])).
% 0.20/0.57  fof(f5,axiom,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.57  fof(f283,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(X0,sK1),X1))) ) | ~spl7_9),
% 0.20/0.57    inference(resolution,[],[f209,f56])).
% 0.20/0.57  fof(f209,plain,(
% 0.20/0.57    ( ! [X0] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))) ) | ~spl7_9),
% 0.20/0.57    inference(avatar_component_clause,[],[f208])).
% 0.20/0.57  fof(f208,plain,(
% 0.20/0.57    spl7_9 <=> ! [X0] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.57  fof(f77,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(definition_unfolding,[],[f62,f67])).
% 0.20/0.57  fof(f67,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f61,f55])).
% 0.20/0.57  fof(f61,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f9])).
% 0.20/0.57  fof(f9,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.20/0.57  fof(f62,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f37])).
% 0.20/0.57  fof(f37,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.57    inference(flattening,[],[f36])).
% 0.20/0.57  fof(f36,plain,(
% 0.20/0.57    ! [X0,X1,X2,X3] : (((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k4_zfmisc_1(X0,X1,X2,X3)) & (k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3) | (k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 0.20/0.57    inference(nnf_transformation,[],[f13])).
% 0.20/0.57  fof(f13,axiom,(
% 0.20/0.57    ! [X0,X1,X2,X3] : ((k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k4_zfmisc_1(X0,X1,X2,X3))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).
% 0.20/0.57  fof(f277,plain,(
% 0.20/0.57    ~spl7_8),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f276])).
% 0.20/0.57  fof(f276,plain,(
% 0.20/0.57    $false | ~spl7_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f275,f40])).
% 0.20/0.57  fof(f275,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl7_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f274,f41])).
% 0.20/0.57  fof(f274,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f273,f42])).
% 0.20/0.57  fof(f273,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_8),
% 0.20/0.57    inference(condensation,[],[f272])).
% 0.20/0.57  fof(f272,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_8),
% 0.20/0.57    inference(subsumption_resolution,[],[f267,f89])).
% 0.20/0.57  fof(f267,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_8),
% 0.20/0.57    inference(superposition,[],[f77,f262])).
% 0.20/0.57  fof(f262,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_8),
% 0.20/0.57    inference(resolution,[],[f253,f83])).
% 0.20/0.57  fof(f253,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_8),
% 0.20/0.57    inference(resolution,[],[f247,f69])).
% 0.20/0.57  fof(f247,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~m1_subset_1(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_8),
% 0.20/0.57    inference(resolution,[],[f244,f52])).
% 0.20/0.57  fof(f244,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~r2_hidden(sK4,k2_zfmisc_1(k2_zfmisc_1(sK0,X0),X1))) ) | ~spl7_8),
% 0.20/0.57    inference(resolution,[],[f206,f56])).
% 0.20/0.57  fof(f206,plain,(
% 0.20/0.57    ( ! [X1] : (~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))) ) | ~spl7_8),
% 0.20/0.57    inference(avatar_component_clause,[],[f205])).
% 0.20/0.57  fof(f205,plain,(
% 0.20/0.57    spl7_8 <=> ! [X1] : ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.57  fof(f238,plain,(
% 0.20/0.57    ~spl7_7),
% 0.20/0.57    inference(avatar_contradiction_clause,[],[f237])).
% 0.20/0.57  fof(f237,plain,(
% 0.20/0.57    $false | ~spl7_7),
% 0.20/0.57    inference(subsumption_resolution,[],[f236,f40])).
% 0.20/0.57  fof(f236,plain,(
% 0.20/0.57    k1_xboole_0 = sK0 | ~spl7_7),
% 0.20/0.57    inference(subsumption_resolution,[],[f235,f41])).
% 0.20/0.57  fof(f235,plain,(
% 0.20/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_7),
% 0.20/0.57    inference(subsumption_resolution,[],[f234,f42])).
% 0.20/0.57  fof(f234,plain,(
% 0.20/0.57    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl7_7),
% 0.20/0.57    inference(condensation,[],[f233])).
% 0.20/0.57  fof(f233,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_7),
% 0.20/0.57    inference(subsumption_resolution,[],[f226,f89])).
% 0.20/0.57  fof(f226,plain,(
% 0.20/0.57    ( ! [X0] : (k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) ) | ~spl7_7),
% 0.20/0.57    inference(superposition,[],[f77,f223])).
% 0.20/0.57  fof(f223,plain,(
% 0.20/0.57    k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2) | ~spl7_7),
% 0.20/0.57    inference(resolution,[],[f217,f83])).
% 0.20/0.57  fof(f217,plain,(
% 0.20/0.57    v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2)) | ~spl7_7),
% 0.20/0.57    inference(resolution,[],[f215,f69])).
% 0.20/0.57  fof(f215,plain,(
% 0.20/0.57    ( ! [X0] : (~m1_subset_1(sK4,k2_zfmisc_1(X0,sK2)) | v1_xboole_0(k2_zfmisc_1(X0,sK2))) ) | ~spl7_7),
% 0.20/0.57    inference(resolution,[],[f203,f52])).
% 0.20/0.57  fof(f203,plain,(
% 0.20/0.57    ( ! [X2] : (~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) ) | ~spl7_7),
% 0.20/0.57    inference(avatar_component_clause,[],[f202])).
% 0.20/0.57  fof(f202,plain,(
% 0.20/0.57    spl7_7 <=> ! [X2] : ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))),
% 0.20/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.57  fof(f214,plain,(
% 0.20/0.57    spl7_7 | spl7_8 | spl7_9 | spl7_10),
% 0.20/0.57    inference(avatar_split_clause,[],[f200,f211,f208,f205,f202])).
% 0.20/0.57  fof(f200,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (sK3 = k2_mcart_1(sK4) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(X0,sK1)) | ~r2_hidden(k1_mcart_1(sK4),k2_zfmisc_1(sK0,X1)) | ~r2_hidden(sK4,k2_zfmisc_1(X2,sK2))) )),
% 0.20/0.57    inference(equality_resolution,[],[f185])).
% 0.20/0.57  fof(f185,plain,(
% 0.20/0.57    ( ! [X2,X0,X5,X1] : (sK4 != X0 | k2_mcart_1(X0) = sK3 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 0.20/0.57    inference(condensation,[],[f183])).
% 0.20/0.57  fof(f183,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4)) | ~r2_hidden(X0,k2_zfmisc_1(X5,sK2))) )),
% 0.20/0.57    inference(resolution,[],[f180,f57])).
% 0.20/0.57  fof(f57,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f26])).
% 0.20/0.57  fof(f180,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK2) | k2_mcart_1(X0) = sK3 | sK4 != X0 | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(X1,sK1)) | ~r2_hidden(k1_mcart_1(X0),k2_zfmisc_1(sK0,X2)) | ~r2_hidden(X0,k2_zfmisc_1(X3,X4))) )),
% 0.20/0.57    inference(superposition,[],[f160,f135])).
% 0.20/0.57  fof(f135,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 0.20/0.57    inference(resolution,[],[f51,f50])).
% 0.20/0.57  fof(f50,plain,(
% 0.20/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.57    inference(cnf_transformation,[],[f6])).
% 0.20/0.57  fof(f6,axiom,(
% 0.20/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.57  fof(f51,plain,(
% 0.20/0.57    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,X1) | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0) )),
% 0.20/0.57    inference(cnf_transformation,[],[f22])).
% 0.20/0.57  fof(f22,plain,(
% 0.20/0.57    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(flattening,[],[f21])).
% 0.20/0.57  fof(f21,plain,(
% 0.20/0.57    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f11])).
% 0.20/0.57  fof(f11,axiom,(
% 0.20/0.57    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).
% 0.20/0.57  fof(f160,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (k4_tarski(X0,X1) != sK4 | sK3 = X1 | ~r2_hidden(X1,sK2) | ~r2_hidden(X0,k2_zfmisc_1(X2,sK1)) | ~r2_hidden(X0,k2_zfmisc_1(sK0,X3))) )),
% 0.20/0.57    inference(resolution,[],[f151,f56])).
% 0.20/0.57  fof(f151,plain,(
% 0.20/0.57    ( ! [X4,X0,X1] : (~r2_hidden(k1_mcart_1(X1),sK0) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,k2_zfmisc_1(X4,sK1))) )),
% 0.20/0.57    inference(condensation,[],[f149])).
% 0.20/0.57  fof(f149,plain,(
% 0.20/0.57    ( ! [X4,X2,X0,X3,X1] : (sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | sK4 != k4_tarski(X1,X0) | ~r2_hidden(k1_mcart_1(X1),sK0) | ~r2_hidden(X0,sK2) | ~r2_hidden(X1,k2_zfmisc_1(X4,sK1))) )),
% 0.20/0.57    inference(resolution,[],[f148,f57])).
% 0.20/0.57  fof(f148,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_mcart_1(X0),sK1) | sK3 = X1 | ~r2_hidden(X0,k2_zfmisc_1(X2,X3)) | k4_tarski(X0,X1) != sK4 | ~r2_hidden(k1_mcart_1(X0),sK0) | ~r2_hidden(X1,sK2)) )),
% 0.20/0.57    inference(resolution,[],[f147,f53])).
% 0.20/0.57  fof(f53,plain,(
% 0.20/0.57    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f25])).
% 0.20/0.57  fof(f25,plain,(
% 0.20/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.57    inference(ennf_transformation,[],[f4])).
% 0.20/0.57  fof(f4,axiom,(
% 0.20/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.57  fof(f147,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(k2_mcart_1(X1),sK1) | ~r2_hidden(k1_mcart_1(X1),sK0)) )),
% 0.20/0.57    inference(resolution,[],[f146,f53])).
% 0.20/0.57  fof(f146,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k1_mcart_1(X1),sK0) | ~m1_subset_1(X0,sK2) | sK4 != k4_tarski(X1,X0) | sK3 = X0 | ~r2_hidden(X1,k2_zfmisc_1(X2,X3)) | ~r2_hidden(k2_mcart_1(X1),sK1)) )),
% 0.20/0.57    inference(resolution,[],[f137,f53])).
% 0.20/0.57  fof(f137,plain,(
% 0.20/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_mcart_1(X0),sK1) | sK3 = X1 | ~m1_subset_1(X1,sK2) | k4_tarski(X0,X1) != sK4 | ~m1_subset_1(k1_mcart_1(X0),sK0) | ~r2_hidden(X0,k2_zfmisc_1(X2,X3))) )),
% 0.20/0.57    inference(superposition,[],[f68,f135])).
% 0.20/0.57  fof(f68,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (sK4 != k4_tarski(k4_tarski(X5,X6),X7) | sK3 = X7 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.57    inference(definition_unfolding,[],[f39,f54])).
% 0.20/0.57  fof(f54,plain,(
% 0.20/0.57    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f7])).
% 0.20/0.57  fof(f7,axiom,(
% 0.20/0.57    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.57  fof(f39,plain,(
% 0.20/0.57    ( ! [X6,X7,X5] : (sK3 = X7 | k3_mcart_1(X5,X6,X7) != sK4 | ~m1_subset_1(X7,sK2) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.57    inference(cnf_transformation,[],[f29])).
% 0.20/0.57  % SZS output end Proof for theBenchmark
% 0.20/0.57  % (29874)------------------------------
% 0.20/0.57  % (29874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (29874)Termination reason: Refutation
% 0.20/0.57  
% 0.20/0.57  % (29874)Memory used [KB]: 10874
% 0.20/0.57  % (29874)Time elapsed: 0.130 s
% 0.20/0.57  % (29874)------------------------------
% 0.20/0.57  % (29874)------------------------------
% 0.20/0.57  % (29865)Success in time 0.202 s
%------------------------------------------------------------------------------
