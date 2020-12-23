%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0383+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:52 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 112 expanded)
%              Number of leaves         :   12 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :  177 ( 336 expanded)
%              Number of equality atoms :   12 (  28 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f31,f55,f64,f79,f101,f106,f108,f120])).

fof(f120,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_6
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_6
    | spl6_10 ),
    inference(subsumption_resolution,[],[f118,f100])).

fof(f100,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl6_10
  <=> m1_subset_1(sK5(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f118,plain,
    ( m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_6 ),
    inference(resolution,[],[f91,f24])).

% (27690)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f24,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl6_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | m1_subset_1(sK5(sK0,sK1,X0),sK1) )
    | ~ spl6_2
    | spl6_6 ),
    inference(resolution,[],[f66,f38])).

fof(f38,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,sK1,X1),sK1)
        | ~ r2_hidden(X1,sK2) )
    | ~ spl6_2 ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK5(X1,X2,X3),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4,X5] :
          ( k4_tarski(X4,X5) = X3
          & r2_hidden(X5,X2)
          & r2_hidden(X4,X1) )
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4,X5] :
            ~ ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X2)
              & r2_hidden(X4,X1) )
        & r2_hidden(X3,X0)
        & r1_tarski(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_zfmisc_1)).

fof(f30,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl6_2
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f66,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | m1_subset_1(X1,sK1) )
    | spl6_6 ),
    inference(resolution,[],[f63,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f63,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_6
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f108,plain,
    ( ~ spl6_1
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(resolution,[],[f54,f24])).

fof(f54,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl6_5
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f106,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_9 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4
    | spl6_9 ),
    inference(subsumption_resolution,[],[f104,f96])).

fof(f96,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_9
  <=> m1_subset_1(sK4(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f104,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | ~ spl6_1
    | ~ spl6_2
    | spl6_4 ),
    inference(resolution,[],[f89,f24])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | m1_subset_1(sK4(sK0,sK1,X0),sK0) )
    | ~ spl6_2
    | spl6_4 ),
    inference(resolution,[],[f58,f37])).

fof(f37,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,sK1,X0),sK0)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl6_2 ),
    inference(resolution,[],[f30,f18])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(sK4(X1,X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f58,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | m1_subset_1(X1,sK0) )
    | spl6_4 ),
    inference(resolution,[],[f51,f15])).

fof(f51,plain,
    ( ~ v1_xboole_0(sK0)
    | spl6_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl6_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f101,plain,
    ( ~ spl6_9
    | ~ spl6_10
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f82,f76,f98,f94])).

fof(f76,plain,
    ( spl6_8
  <=> sK3 = k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f82,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | ~ spl6_8 ),
    inference(trivial_inequality_removal,[],[f81])).

fof(f81,plain,
    ( sK3 != sK3
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK3),sK0)
    | ~ spl6_8 ),
    inference(superposition,[],[f10,f78])).

fof(f78,plain,
    ( sK3 = k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f76])).

fof(f10,plain,(
    ! [X4,X5] :
      ( k4_tarski(X4,X5) != sK3
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ! [X5] :
              ( k4_tarski(X4,X5) != X3
              | ~ m1_subset_1(X5,X1) )
          | ~ m1_subset_1(X4,X0) )
      & r1_tarski(X2,k2_zfmisc_1(X0,X1))
      & r2_hidden(X3,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( ! [X4] :
              ( m1_subset_1(X4,X0)
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => k4_tarski(X4,X5) != X3 ) )
          & r1_tarski(X2,k2_zfmisc_1(X0,X1))
          & r2_hidden(X3,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( ! [X4] :
            ( m1_subset_1(X4,X0)
           => ! [X5] :
                ( m1_subset_1(X5,X1)
               => k4_tarski(X4,X5) != X3 ) )
        & r1_tarski(X2,k2_zfmisc_1(X0,X1))
        & r2_hidden(X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_subset_1)).

fof(f79,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f56,f28,f22,f76])).

fof(f56,plain,
    ( sK3 = k4_tarski(sK4(sK0,sK1,sK3),sK5(sK0,sK1,sK3))
    | ~ spl6_1
    | ~ spl6_2 ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | k4_tarski(sK4(sK0,sK1,X2),sK5(sK0,sK1,X2)) = X2 )
    | ~ spl6_2 ),
    inference(resolution,[],[f30,f20])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ r2_hidden(X3,X0)
      | k4_tarski(sK4(X1,X2,X3),sK5(X1,X2,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f64,plain,
    ( ~ spl6_6
    | spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f47,f28,f53,f61])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(sK1) )
    | ~ spl6_2 ),
    inference(resolution,[],[f38,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f55,plain,
    ( ~ spl6_4
    | spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f46,f28,f53,f49])).

fof(f46,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(sK0) )
    | ~ spl6_2 ),
    inference(resolution,[],[f37,f17])).

fof(f31,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f12,f28])).

fof(f12,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f11,f22])).

fof(f11,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
