%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 194 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :  304 ( 859 expanded)
%              Number of equality atoms :    9 (  16 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f159,f179,f206,f224,f297,f316,f323])).

fof(f323,plain,(
    ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl6_22 ),
    inference(resolution,[],[f292,f106])).

fof(f106,plain,(
    ~ r2_hidden(sK4(sK1,sK2),sK2) ),
    inference(resolution,[],[f39,f30])).

fof(f30,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK1,sK2)
    & ! [X3] :
        ( r2_hidden(X3,sK2)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12,f11])).

% (28394)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f11,plain,
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

fof(f12,plain,
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

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & ! [X3] :
              ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                   => r2_hidden(X3,X2) ) )
             => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f292,plain,
    ( r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl6_22
  <=> r2_hidden(sK4(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f316,plain,
    ( ~ spl6_13
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl6_13
    | spl6_23 ),
    inference(resolution,[],[f307,f30])).

fof(f307,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl6_13
    | spl6_23 ),
    inference(resolution,[],[f299,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f299,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK1)
    | ~ spl6_13
    | spl6_23 ),
    inference(resolution,[],[f296,f158])).

fof(f158,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl6_13
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f296,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK0)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f294])).

fof(f294,plain,
    ( spl6_23
  <=> r2_hidden(sK4(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f297,plain,
    ( spl6_22
    | ~ spl6_23
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f287,f65,f294,f290])).

fof(f65,plain,
    ( spl6_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f287,plain,
    ( ~ r2_hidden(sK4(sK1,sK2),sK0)
    | r2_hidden(sK4(sK1,sK2),sK2)
    | ~ spl6_4 ),
    inference(resolution,[],[f242,f30])).

fof(f242,plain,
    ( ! [X1] :
        ( r1_tarski(sK1,X1)
        | ~ r2_hidden(sK4(sK1,X1),sK0)
        | r2_hidden(sK4(sK1,X1),sK2) )
    | ~ spl6_4 ),
    inference(resolution,[],[f66,f38])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f224,plain,
    ( ~ spl6_3
    | spl6_9
    | ~ spl6_13 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | ~ spl6_3
    | spl6_9
    | ~ spl6_13 ),
    inference(resolution,[],[f217,f97])).

fof(f97,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f217,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f211,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
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

fof(f211,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1)
    | ~ spl6_3
    | ~ spl6_13 ),
    inference(resolution,[],[f209,f158])).

fof(f209,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f63,f31])).

fof(f31,plain,(
    ! [X2,X0] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( v1_xboole_0(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl6_3
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f206,plain,(
    ~ spl6_9 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl6_9 ),
    inference(resolution,[],[f203,f30])).

fof(f203,plain,
    ( ! [X1] : r1_tarski(sK1,X1)
    | ~ spl6_9 ),
    inference(resolution,[],[f200,f38])).

fof(f200,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl6_9 ),
    inference(resolution,[],[f98,f31])).

fof(f98,plain,
    ( v1_xboole_0(sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f179,plain,(
    ~ spl6_12 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | ~ spl6_12 ),
    inference(resolution,[],[f167,f165])).

fof(f165,plain,
    ( ! [X0] : ~ r1_tarski(X0,sK0)
    | ~ spl6_12 ),
    inference(resolution,[],[f155,f44])).

fof(f44,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).

% (28400)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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

fof(f155,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_zfmisc_1(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_12
  <=> ! [X1] : ~ r2_hidden(X1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f167,plain,
    ( ! [X2] : r1_tarski(k1_zfmisc_1(sK0),X2)
    | ~ spl6_12 ),
    inference(resolution,[],[f155,f38])).

fof(f159,plain,
    ( spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f148,f157,f154])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0)
      | ~ r2_hidden(X1,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f135,f27])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f135,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(X12))
      | ~ r2_hidden(X10,X11)
      | r2_hidden(X10,X12)
      | ~ r2_hidden(X13,k1_zfmisc_1(X12)) ) ),
    inference(resolution,[],[f123,f31])).

fof(f123,plain,(
    ! [X6,X7,X5] :
      ( v1_xboole_0(k1_zfmisc_1(X6))
      | ~ r2_hidden(X5,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
      | r2_hidden(X5,X6) ) ),
    inference(resolution,[],[f119,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f119,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X5))
      | r2_hidden(X3,X5)
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f37,f45])).

fof(f45,plain,(
    ! [X0,X3] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f22])).

% (28401)Termination reason: Refutation not found, incomplete strategy
fof(f67,plain,
    ( spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f58,f65,f61])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0)
      | ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f34,f29])).

% (28401)Memory used [KB]: 10746
% (28401)Time elapsed: 0.110 s
fof(f29,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f13])).

% (28401)------------------------------
% (28401)------------------------------
% (28403)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:34:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (28393)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (28409)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.51  % (28393)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (28385)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (28401)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.51  % (28401)Refutation not found, incomplete strategy% (28401)------------------------------
% 0.21/0.51  % (28401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f324,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f67,f159,f179,f206,f224,f297,f316,f323])).
% 0.21/0.51  fof(f323,plain,(
% 0.21/0.51    ~spl6_22),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f321])).
% 0.21/0.51  fof(f321,plain,(
% 0.21/0.51    $false | ~spl6_22),
% 0.21/0.51    inference(resolution,[],[f292,f106])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1,sK2),sK2)),
% 0.21/0.51    inference(resolution,[],[f39,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ~r1_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12,f11])).
% 0.21/0.51  % (28394)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X2] : (~r1_tarski(sK1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (~r1_tarski(sK1,sK2) & ! [X3] : (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : (~r1_tarski(X1,X2) & ! [X3] : (r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(flattening,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1] : (? [X2] : ((~r1_tarski(X1,X2) & ! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f5])).
% 0.21/0.51  fof(f5,conjecture,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK4(X0,X1),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    r2_hidden(sK4(sK1,sK2),sK2) | ~spl6_22),
% 0.21/0.51    inference(avatar_component_clause,[],[f290])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    spl6_22 <=> r2_hidden(sK4(sK1,sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    ~spl6_13 | spl6_23),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f314])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    $false | (~spl6_13 | spl6_23)),
% 0.21/0.51    inference(resolution,[],[f307,f30])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    r1_tarski(sK1,sK2) | (~spl6_13 | spl6_23)),
% 0.21/0.51    inference(resolution,[],[f299,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1,sK2),sK1) | (~spl6_13 | spl6_23)),
% 0.21/0.51    inference(resolution,[],[f296,f158])).
% 0.21/0.51  fof(f158,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1)) ) | ~spl6_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f157])).
% 0.21/0.51  fof(f157,plain,(
% 0.21/0.51    spl6_13 <=> ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1,sK2),sK0) | spl6_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f294])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    spl6_23 <=> r2_hidden(sK4(sK1,sK2),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    spl6_22 | ~spl6_23 | ~spl6_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f287,f65,f294,f290])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl6_4 <=> ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    ~r2_hidden(sK4(sK1,sK2),sK0) | r2_hidden(sK4(sK1,sK2),sK2) | ~spl6_4),
% 0.21/0.51    inference(resolution,[],[f242,f30])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(sK1,X1) | ~r2_hidden(sK4(sK1,X1),sK0) | r2_hidden(sK4(sK1,X1),sK2)) ) | ~spl6_4),
% 0.21/0.51    inference(resolution,[],[f66,f38])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0)) ) | ~spl6_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f65])).
% 0.21/0.51  fof(f224,plain,(
% 0.21/0.51    ~spl6_3 | spl6_9 | ~spl6_13),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f220])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    $false | (~spl6_3 | spl6_9 | ~spl6_13)),
% 0.21/0.51    inference(resolution,[],[f217,f97])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1) | spl6_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f96])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl6_9 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | (~spl6_3 | ~spl6_13)),
% 0.21/0.51    inference(resolution,[],[f211,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(rectify,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f211,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK1)) ) | (~spl6_3 | ~spl6_13)),
% 0.21/0.52    inference(resolution,[],[f209,f158])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK0)) ) | ~spl6_3),
% 0.21/0.52    inference(resolution,[],[f63,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X2,X0] : (~v1_xboole_0(X0) | ~r2_hidden(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v1_xboole_0(sK0) | ~spl6_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    spl6_3 <=> v1_xboole_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    ~spl6_9),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f204])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    $false | ~spl6_9),
% 0.21/0.52    inference(resolution,[],[f203,f30])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(sK1,X1)) ) | ~spl6_9),
% 0.21/0.52    inference(resolution,[],[f200,f38])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl6_9),
% 0.21/0.52    inference(resolution,[],[f98,f31])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    v1_xboole_0(sK1) | ~spl6_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ~spl6_12),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f178])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    $false | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f167,f165])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,sK0)) ) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f155,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f24,f25])).
% 0.21/0.52  % (28400)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    ( ! [X1] : (~r2_hidden(X1,k1_zfmisc_1(sK0))) ) | ~spl6_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f154])).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl6_12 <=> ! [X1] : ~r2_hidden(X1,k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ( ! [X2] : (r1_tarski(k1_zfmisc_1(sK0),X2)) ) | ~spl6_12),
% 0.21/0.52    inference(resolution,[],[f155,f38])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    spl6_12 | spl6_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f148,f157,f154])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0) | ~r2_hidden(X1,k1_zfmisc_1(sK0))) )),
% 0.21/0.52    inference(resolution,[],[f135,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X12,X10,X13,X11] : (~m1_subset_1(X11,k1_zfmisc_1(X12)) | ~r2_hidden(X10,X11) | r2_hidden(X10,X12) | ~r2_hidden(X13,k1_zfmisc_1(X12))) )),
% 0.21/0.52    inference(resolution,[],[f123,f31])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (v1_xboole_0(k1_zfmisc_1(X6)) | ~r2_hidden(X5,X7) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | r2_hidden(X5,X6)) )),
% 0.21/0.52    inference(resolution,[],[f119,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(nnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,plain,(
% 0.21/0.52    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~r2_hidden(X4,k1_zfmisc_1(X5)) | r2_hidden(X3,X5) | ~r2_hidden(X3,X4)) )),
% 0.21/0.52    inference(resolution,[],[f37,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X3] : (r1_tarski(X3,X0) | ~r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(equality_resolution,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  % (28401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl6_3 | spl6_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f65,f61])).
% 0.21/0.52  
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK0) | v1_xboole_0(sK0) | ~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 0.21/0.52    inference(resolution,[],[f34,f29])).
% 0.21/0.52  % (28401)Memory used [KB]: 10746
% 0.21/0.52  % (28401)Time elapsed: 0.110 s
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  % (28401)------------------------------
% 0.21/0.52  % (28401)------------------------------
% 0.21/0.52  % (28403)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f18])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (28393)------------------------------
% 0.21/0.52  % (28393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28393)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (28393)Memory used [KB]: 6396
% 0.21/0.52  % (28393)Time elapsed: 0.103 s
% 0.21/0.52  % (28393)------------------------------
% 0.21/0.52  % (28393)------------------------------
% 0.21/0.52  % (28378)Success in time 0.16 s
%------------------------------------------------------------------------------
