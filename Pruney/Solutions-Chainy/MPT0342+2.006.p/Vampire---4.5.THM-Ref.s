%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:40 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 179 expanded)
%              Number of leaves         :   16 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  279 ( 789 expanded)
%              Number of equality atoms :    9 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f335,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f93,f279,f299,f309,f314,f331,f334])).

fof(f334,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | ~ spl5_8 ),
    inference(resolution,[],[f294,f30])).

% (25158)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f30,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK1,sK2)
    & ! [X3] :
        ( r2_hidden(X3,sK2)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X1,X2)
            & ! [X3] :
                ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(sK1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,sK1)
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r1_tarski(sK1,X2)
        & ! [X3] :
            ( r2_hidden(X3,X2)
            | ~ r2_hidden(X3,sK1)
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( ~ r1_tarski(sK1,sK2)
      & ! [X3] :
          ( r2_hidden(X3,sK2)
          | ~ r2_hidden(X3,sK1)
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                   => r2_hidden(X3,X2) ) )
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f294,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl5_8
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f331,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | ~ spl5_1 ),
    inference(resolution,[],[f318,f130])).

fof(f130,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f38,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f318,plain,
    ( ! [X0] : ~ r1_tarski(X0,sK0)
    | ~ spl5_1 ),
    inference(resolution,[],[f317,f46])).

fof(f46,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f317,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(resolution,[],[f64,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f64,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_1
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f314,plain,
    ( ~ spl5_2
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f311])).

fof(f311,plain,
    ( $false
    | ~ spl5_2
    | spl5_10 ),
    inference(resolution,[],[f310,f68])).

fof(f68,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_2
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f310,plain,
    ( ~ r2_hidden(sK1,k1_zfmisc_1(sK0))
    | spl5_10 ),
    inference(resolution,[],[f308,f47])).

% (25166)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f47,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f308,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl5_10
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f309,plain,
    ( spl5_8
    | ~ spl5_10
    | spl5_9 ),
    inference(avatar_split_clause,[],[f303,f296,f306,f292])).

fof(f296,plain,
    ( spl5_9
  <=> r2_hidden(sK3(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f303,plain,
    ( ~ r1_tarski(sK1,sK0)
    | r1_tarski(sK1,sK2)
    | spl5_9 ),
    inference(resolution,[],[f298,f147])).

fof(f147,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(sK3(X8,X9),X10)
      | ~ r1_tarski(X8,X10)
      | r1_tarski(X8,X9) ) ),
    inference(resolution,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f298,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f296])).

fof(f299,plain,
    ( spl5_8
    | ~ spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f290,f91,f296,f292])).

fof(f91,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f290,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ~ r2_hidden(sK3(sK1,sK2),sK0)
    | r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f281,f37])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(X0,sK2),sK1)
        | ~ r2_hidden(sK3(X0,sK2),sK0)
        | r1_tarski(X0,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f92,f38])).

fof(f92,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f279,plain,
    ( ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f270,f30])).

fof(f270,plain,
    ( ! [X4] : r1_tarski(sK1,X4)
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f263,f68])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_zfmisc_1(sK0))
        | r1_tarski(X0,X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f261,f47])).

fof(f261,plain,
    ( ! [X6,X7] :
        ( ~ r1_tarski(X6,sK0)
        | r1_tarski(X6,X7) )
    | ~ spl5_4 ),
    inference(resolution,[],[f147,f96])).

fof(f96,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f89,f45])).

fof(f89,plain,
    ( v1_xboole_0(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f93,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f83,f91,f87])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f69,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f59,f66,f62])).

fof(f59,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f32,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.40/0.55  % (25148)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.40/0.55  % (25148)Refutation not found, incomplete strategy% (25148)------------------------------
% 1.40/0.55  % (25148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (25148)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (25148)Memory used [KB]: 1663
% 1.40/0.55  % (25148)Time elapsed: 0.120 s
% 1.40/0.55  % (25148)------------------------------
% 1.40/0.55  % (25148)------------------------------
% 1.40/0.56  % (25176)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.56  % (25160)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.56  % (25152)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.56  % (25151)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.57  % (25169)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.57  % (25160)Refutation found. Thanks to Tanya!
% 1.58/0.57  % SZS status Theorem for theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f335,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(avatar_sat_refutation,[],[f69,f93,f279,f299,f309,f314,f331,f334])).
% 1.58/0.57  fof(f334,plain,(
% 1.58/0.57    ~spl5_8),
% 1.58/0.57    inference(avatar_contradiction_clause,[],[f333])).
% 1.58/0.57  fof(f333,plain,(
% 1.58/0.57    $false | ~spl5_8),
% 1.58/0.57    inference(resolution,[],[f294,f30])).
% 1.58/0.57  % (25158)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.57  fof(f30,plain,(
% 1.58/0.57    ~r1_tarski(sK1,sK2)),
% 1.58/0.57    inference(cnf_transformation,[],[f16])).
% 1.58/0.58  fof(f16,plain,(
% 1.58/0.58    (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f15,f14])).
% 1.58/0.58  fof(f14,plain,(
% 1.58/0.58    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f15,plain,(
% 1.58/0.58    ? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f10,plain,(
% 1.58/0.58    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.58/0.58    inference(flattening,[],[f9])).
% 1.58/0.58  fof(f9,plain,(
% 1.58/0.58    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & ! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f8])).
% 1.58/0.58  fof(f8,negated_conjecture,(
% 1.58/0.58    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.58/0.58    inference(negated_conjecture,[],[f7])).
% 1.58/0.58  fof(f7,conjecture,(
% 1.58/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 1.58/0.58  fof(f294,plain,(
% 1.58/0.58    r1_tarski(sK1,sK2) | ~spl5_8),
% 1.58/0.58    inference(avatar_component_clause,[],[f292])).
% 1.58/0.58  fof(f292,plain,(
% 1.58/0.58    spl5_8 <=> r1_tarski(sK1,sK2)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.58/0.58  fof(f331,plain,(
% 1.58/0.58    ~spl5_1),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f328])).
% 1.58/0.58  fof(f328,plain,(
% 1.58/0.58    $false | ~spl5_1),
% 1.58/0.58    inference(resolution,[],[f318,f130])).
% 1.58/0.58  fof(f130,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f127])).
% 1.58/0.58  fof(f127,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.58/0.58    inference(resolution,[],[f38,f37])).
% 1.58/0.58  fof(f37,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f21])).
% 1.58/0.58  fof(f21,plain,(
% 1.58/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f20])).
% 1.58/0.58  fof(f20,plain,(
% 1.58/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f19,plain,(
% 1.58/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.58    inference(rectify,[],[f18])).
% 1.58/0.58  fof(f18,plain,(
% 1.58/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.58/0.58    inference(nnf_transformation,[],[f12])).
% 1.58/0.58  fof(f12,plain,(
% 1.58/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f1])).
% 1.58/0.58  fof(f1,axiom,(
% 1.58/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.58  fof(f38,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f21])).
% 1.58/0.58  fof(f318,plain,(
% 1.58/0.58    ( ! [X0] : (~r1_tarski(X0,sK0)) ) | ~spl5_1),
% 1.58/0.58    inference(resolution,[],[f317,f46])).
% 1.58/0.58  fof(f46,plain,(
% 1.58/0.58    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.58/0.58    inference(equality_resolution,[],[f40])).
% 1.58/0.58  fof(f40,plain,(
% 1.58/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f25])).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f23,f24])).
% 1.58/0.58  fof(f24,plain,(
% 1.58/0.58    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f23,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.58/0.58    inference(rectify,[],[f22])).
% 1.58/0.58  fof(f22,plain,(
% 1.58/0.58    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.58/0.58    inference(nnf_transformation,[],[f3])).
% 1.58/0.58  fof(f3,axiom,(
% 1.58/0.58    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.58/0.58  fof(f317,plain,(
% 1.58/0.58    ( ! [X2] : (~r2_hidden(X2,k1_zfmisc_1(sK0))) ) | ~spl5_1),
% 1.58/0.58    inference(resolution,[],[f64,f45])).
% 1.58/0.58  fof(f45,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f13])).
% 1.58/0.58  fof(f13,plain,(
% 1.58/0.58    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f2])).
% 1.58/0.58  fof(f2,axiom,(
% 1.58/0.58    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 1.58/0.58  fof(f64,plain,(
% 1.58/0.58    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_1),
% 1.58/0.58    inference(avatar_component_clause,[],[f62])).
% 1.58/0.58  fof(f62,plain,(
% 1.58/0.58    spl5_1 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.58/0.58  fof(f314,plain,(
% 1.58/0.58    ~spl5_2 | spl5_10),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f311])).
% 1.58/0.58  fof(f311,plain,(
% 1.58/0.58    $false | (~spl5_2 | spl5_10)),
% 1.58/0.58    inference(resolution,[],[f310,f68])).
% 1.58/0.58  fof(f68,plain,(
% 1.58/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.58/0.58    inference(avatar_component_clause,[],[f66])).
% 1.58/0.58  fof(f66,plain,(
% 1.58/0.58    spl5_2 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.58/0.58  fof(f310,plain,(
% 1.58/0.58    ~r2_hidden(sK1,k1_zfmisc_1(sK0)) | spl5_10),
% 1.58/0.58    inference(resolution,[],[f308,f47])).
% 1.58/0.58  % (25166)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.58  fof(f47,plain,(
% 1.58/0.58    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 1.58/0.58    inference(equality_resolution,[],[f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f25])).
% 1.58/0.58  fof(f308,plain,(
% 1.58/0.58    ~r1_tarski(sK1,sK0) | spl5_10),
% 1.58/0.58    inference(avatar_component_clause,[],[f306])).
% 1.58/0.58  fof(f306,plain,(
% 1.58/0.58    spl5_10 <=> r1_tarski(sK1,sK0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.58/0.58  fof(f309,plain,(
% 1.58/0.58    spl5_8 | ~spl5_10 | spl5_9),
% 1.58/0.58    inference(avatar_split_clause,[],[f303,f296,f306,f292])).
% 1.58/0.58  fof(f296,plain,(
% 1.58/0.58    spl5_9 <=> r2_hidden(sK3(sK1,sK2),sK0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.58/0.58  fof(f303,plain,(
% 1.58/0.58    ~r1_tarski(sK1,sK0) | r1_tarski(sK1,sK2) | spl5_9),
% 1.58/0.58    inference(resolution,[],[f298,f147])).
% 1.58/0.58  fof(f147,plain,(
% 1.58/0.58    ( ! [X10,X8,X9] : (r2_hidden(sK3(X8,X9),X10) | ~r1_tarski(X8,X10) | r1_tarski(X8,X9)) )),
% 1.58/0.58    inference(resolution,[],[f36,f37])).
% 1.58/0.58  fof(f36,plain,(
% 1.58/0.58    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f21])).
% 1.58/0.58  fof(f298,plain,(
% 1.58/0.58    ~r2_hidden(sK3(sK1,sK2),sK0) | spl5_9),
% 1.58/0.58    inference(avatar_component_clause,[],[f296])).
% 1.58/0.58  fof(f299,plain,(
% 1.58/0.58    spl5_8 | ~spl5_9 | ~spl5_5),
% 1.58/0.58    inference(avatar_split_clause,[],[f290,f91,f296,f292])).
% 1.58/0.58  fof(f91,plain,(
% 1.58/0.58    spl5_5 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1))),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.58/0.58  fof(f290,plain,(
% 1.58/0.58    ~r2_hidden(sK3(sK1,sK2),sK0) | r1_tarski(sK1,sK2) | ~spl5_5),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f286])).
% 1.58/0.58  fof(f286,plain,(
% 1.58/0.58    ~r2_hidden(sK3(sK1,sK2),sK0) | r1_tarski(sK1,sK2) | r1_tarski(sK1,sK2) | ~spl5_5),
% 1.58/0.58    inference(resolution,[],[f281,f37])).
% 1.58/0.58  fof(f281,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(sK3(X0,sK2),sK1) | ~r2_hidden(sK3(X0,sK2),sK0) | r1_tarski(X0,sK2)) ) | ~spl5_5),
% 1.58/0.58    inference(resolution,[],[f92,f38])).
% 1.58/0.58  fof(f92,plain,(
% 1.58/0.58    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl5_5),
% 1.58/0.58    inference(avatar_component_clause,[],[f91])).
% 1.58/0.58  fof(f279,plain,(
% 1.58/0.58    ~spl5_2 | ~spl5_4),
% 1.58/0.58    inference(avatar_contradiction_clause,[],[f277])).
% 1.58/0.58  fof(f277,plain,(
% 1.58/0.58    $false | (~spl5_2 | ~spl5_4)),
% 1.58/0.58    inference(resolution,[],[f270,f30])).
% 1.58/0.58  fof(f270,plain,(
% 1.58/0.58    ( ! [X4] : (r1_tarski(sK1,X4)) ) | (~spl5_2 | ~spl5_4)),
% 1.58/0.58    inference(resolution,[],[f263,f68])).
% 1.58/0.58  fof(f263,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,X1)) ) | ~spl5_4),
% 1.58/0.58    inference(resolution,[],[f261,f47])).
% 1.58/0.58  fof(f261,plain,(
% 1.58/0.58    ( ! [X6,X7] : (~r1_tarski(X6,sK0) | r1_tarski(X6,X7)) ) | ~spl5_4),
% 1.58/0.58    inference(resolution,[],[f147,f96])).
% 1.58/0.58  fof(f96,plain,(
% 1.58/0.58    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl5_4),
% 1.58/0.58    inference(resolution,[],[f89,f45])).
% 1.58/0.58  fof(f89,plain,(
% 1.58/0.58    v1_xboole_0(sK0) | ~spl5_4),
% 1.58/0.58    inference(avatar_component_clause,[],[f87])).
% 1.58/0.58  fof(f87,plain,(
% 1.58/0.58    spl5_4 <=> v1_xboole_0(sK0)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.58/0.58  fof(f93,plain,(
% 1.58/0.58    spl5_4 | spl5_5),
% 1.58/0.58    inference(avatar_split_clause,[],[f83,f91,f87])).
% 1.58/0.58  fof(f83,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_xboole_0(sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 1.58/0.58    inference(resolution,[],[f33,f29])).
% 1.58/0.58  fof(f29,plain,(
% 1.58/0.58    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f16])).
% 1.58/0.58  fof(f33,plain,(
% 1.58/0.58    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f17])).
% 1.58/0.58  fof(f17,plain,(
% 1.58/0.58    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.58/0.58    inference(nnf_transformation,[],[f11])).
% 1.58/0.58  fof(f11,plain,(
% 1.58/0.58    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f6])).
% 1.58/0.58  fof(f6,axiom,(
% 1.58/0.58    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.58/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 1.58/0.58  fof(f69,plain,(
% 1.58/0.58    spl5_1 | spl5_2),
% 1.58/0.58    inference(avatar_split_clause,[],[f59,f66,f62])).
% 1.58/0.58  fof(f59,plain,(
% 1.58/0.58    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.58/0.58    inference(resolution,[],[f32,f27])).
% 1.58/0.58  fof(f27,plain,(
% 1.58/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.58/0.58    inference(cnf_transformation,[],[f16])).
% 1.58/0.58  fof(f32,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f17])).
% 1.58/0.58  % SZS output end Proof for theBenchmark
% 1.58/0.58  % (25160)------------------------------
% 1.58/0.58  % (25160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (25160)Termination reason: Refutation
% 1.58/0.58  
% 1.58/0.58  % (25160)Memory used [KB]: 6396
% 1.58/0.58  % (25160)Time elapsed: 0.148 s
% 1.58/0.58  % (25160)------------------------------
% 1.58/0.58  % (25160)------------------------------
% 1.58/0.58  % (25147)Success in time 0.219 s
%------------------------------------------------------------------------------
