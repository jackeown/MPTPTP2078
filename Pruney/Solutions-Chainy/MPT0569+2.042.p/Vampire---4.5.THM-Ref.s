%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:32 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 170 expanded)
%              Number of leaves         :   24 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  329 ( 621 expanded)
%              Number of equality atoms :   27 (  58 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f764,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f77,f83,f209,f214,f290,f295,f305,f438,f763])).

fof(f763,plain,
    ( ~ spl7_3
    | ~ spl7_21
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f760,f303,f292,f287,f74,f287,f74])).

fof(f74,plain,
    ( spl7_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f287,plain,
    ( spl7_21
  <=> r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f292,plain,
    ( spl7_22
  <=> r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f303,plain,
    ( spl7_24
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f760,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(superposition,[],[f600,f56])).

fof(f56,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f600,plain,
    ( ! [X0] : ~ r2_hidden(sK2(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))
    | ~ spl7_3
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f76,f545,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

% (10176)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f545,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK2(k2_relat_1(sK1),sK0)),sK1)
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_24 ),
    inference(unit_resulting_resolution,[],[f88,f294,f289,f304])).

fof(f304,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,sK0) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f303])).

fof(f289,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f287])).

fof(f294,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f292])).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f84,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

% (10156)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
fof(f84,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f49,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f76,plain,
    ( v1_relat_1(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f438,plain,
    ( ~ spl7_13
    | ~ spl7_2
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f433,f206,f68,f211])).

fof(f211,plain,
    ( spl7_13
  <=> r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f68,plain,
    ( spl7_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f206,plain,
    ( spl7_12
  <=> r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f433,plain,
    ( ~ r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1))
    | ~ spl7_2
    | ~ spl7_12 ),
    inference(resolution,[],[f208,f311])).

fof(f311,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK1)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f69,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f69,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f208,plain,
    ( r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f305,plain,
    ( ~ spl7_3
    | spl7_24
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f301,f64,f303,f74])).

fof(f64,plain,
    ( spl7_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f301,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X1,sK0)
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK1))
        | ~ v1_relat_1(sK1) )
    | ~ spl7_1 ),
    inference(superposition,[],[f53,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

% (10179)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
            & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2)
        & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f295,plain,
    ( spl7_22
    | spl7_2 ),
    inference(avatar_split_clause,[],[f284,f68,f292])).

fof(f284,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f70,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f290,plain,
    ( spl7_21
    | spl7_2 ),
    inference(avatar_split_clause,[],[f285,f68,f287])).

fof(f285,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f70,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f214,plain,
    ( spl7_13
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f193,f80,f74,f211])).

fof(f80,plain,
    ( spl7_4
  <=> r2_hidden(sK5(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f193,plain,
    ( r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f76,f82,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f82,plain,
    ( r2_hidden(sK5(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f209,plain,
    ( spl7_12
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f194,f80,f74,f206])).

fof(f194,plain,
    ( r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),sK0)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f76,f82,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK4(X0,X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,
    ( spl7_4
    | spl7_1 ),
    inference(avatar_split_clause,[],[f78,f64,f80])).

fof(f78,plain,
    ( r2_hidden(sK5(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f66,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f66,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f77,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 != k10_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k2_relat_1(sK1),sK0)
      | k1_xboole_0 = k10_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).

% (10177)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f25,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 = k10_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 != k10_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k2_relat_1(sK1),sK0)
        | k1_xboole_0 = k10_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 != k10_relat_1(X1,X0) )
      & ( r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f72,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f42,f68,f64])).

fof(f42,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f71,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f43,f68,f64])).

fof(f43,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:27:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (10161)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  % (10170)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (10159)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.54  % (10158)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.54  % (10161)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % (10157)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.55  % (10165)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f764,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f71,f72,f77,f83,f209,f214,f290,f295,f305,f438,f763])).
% 0.22/0.55  fof(f763,plain,(
% 0.22/0.55    ~spl7_3 | ~spl7_21 | ~spl7_3 | ~spl7_21 | ~spl7_22 | ~spl7_24),
% 0.22/0.55    inference(avatar_split_clause,[],[f760,f303,f292,f287,f74,f287,f74])).
% 0.22/0.55  fof(f74,plain,(
% 0.22/0.55    spl7_3 <=> v1_relat_1(sK1)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.55  fof(f287,plain,(
% 0.22/0.55    spl7_21 <=> r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.55  fof(f292,plain,(
% 0.22/0.55    spl7_22 <=> r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.55  fof(f303,plain,(
% 0.22/0.55    spl7_24 <=> ! [X1,X0] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.55  fof(f760,plain,(
% 0.22/0.55    ~r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK1) | (~spl7_3 | ~spl7_21 | ~spl7_22 | ~spl7_24)),
% 0.22/0.55    inference(superposition,[],[f600,f56])).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.55    inference(ennf_transformation,[],[f7])).
% 0.22/0.55  fof(f7,axiom,(
% 0.22/0.55    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.22/0.55  fof(f600,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(sK2(k2_relat_1(sK1),sK0),k9_relat_1(sK1,X0))) ) | (~spl7_3 | ~spl7_21 | ~spl7_22 | ~spl7_24)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f76,f545,f60])).
% 0.22/0.55  fof(f60,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f40])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f39])).
% 0.22/0.55  fof(f39,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK6(X0,X1,X2),X0),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X2))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(rectify,[],[f37])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f22])).
% 0.22/0.55  % (10176)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f6])).
% 0.22/0.55  fof(f6,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.55  fof(f545,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK2(k2_relat_1(sK1),sK0)),sK1)) ) | (~spl7_21 | ~spl7_22 | ~spl7_24)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f88,f294,f289,f304])).
% 0.22/0.55  fof(f304,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,sK0)) ) | ~spl7_24),
% 0.22/0.55    inference(avatar_component_clause,[],[f303])).
% 0.22/0.55  fof(f289,plain,(
% 0.22/0.55    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | ~spl7_21),
% 0.22/0.55    inference(avatar_component_clause,[],[f287])).
% 0.22/0.55  fof(f294,plain,(
% 0.22/0.55    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | ~spl7_22),
% 0.22/0.55    inference(avatar_component_clause,[],[f292])).
% 0.22/0.55  fof(f88,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(forward_demodulation,[],[f84,f58])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.55  % (10156)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f49,f48])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f30])).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f13])).
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,axiom,(
% 0.22/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    v1_relat_1(sK1) | ~spl7_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f74])).
% 0.22/0.55  fof(f438,plain,(
% 0.22/0.55    ~spl7_13 | ~spl7_2 | ~spl7_12),
% 0.22/0.55    inference(avatar_split_clause,[],[f433,f206,f68,f211])).
% 0.22/0.55  fof(f211,plain,(
% 0.22/0.55    spl7_13 <=> r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.55  fof(f68,plain,(
% 0.22/0.55    spl7_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.55  fof(f206,plain,(
% 0.22/0.55    spl7_12 <=> r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.55  fof(f433,plain,(
% 0.22/0.55    ~r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1)) | (~spl7_2 | ~spl7_12)),
% 0.22/0.55    inference(resolution,[],[f208,f311])).
% 0.22/0.55  fof(f311,plain,(
% 0.22/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r2_hidden(X0,k2_relat_1(sK1))) ) | ~spl7_2),
% 0.22/0.55    inference(resolution,[],[f69,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    inference(rectify,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.55  fof(f69,plain,(
% 0.22/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f208,plain,(
% 0.22/0.55    r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),sK0) | ~spl7_12),
% 0.22/0.55    inference(avatar_component_clause,[],[f206])).
% 0.22/0.55  fof(f305,plain,(
% 0.22/0.55    ~spl7_3 | spl7_24 | ~spl7_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f301,f64,f303,f74])).
% 0.22/0.55  fof(f64,plain,(
% 0.22/0.55    spl7_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.55  fof(f301,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X1,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X1,k2_relat_1(sK1)) | ~v1_relat_1(sK1)) ) | ~spl7_1),
% 0.22/0.55    inference(superposition,[],[f53,f65])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f64])).
% 0.22/0.55  % (10179)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f34,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK4(X0,X1,X2)),X2) & r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2))))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(rectify,[],[f31])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(nnf_transformation,[],[f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.55    inference(ennf_transformation,[],[f8])).
% 0.22/0.55  fof(f8,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.22/0.55  fof(f295,plain,(
% 0.22/0.55    spl7_22 | spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f284,f68,f292])).
% 0.22/0.55  fof(f284,plain,(
% 0.22/0.55    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl7_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f70,f45])).
% 0.22/0.55  fof(f45,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl7_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f68])).
% 0.22/0.55  fof(f290,plain,(
% 0.22/0.55    spl7_21 | spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f285,f68,f287])).
% 0.22/0.55  fof(f285,plain,(
% 0.22/0.55    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl7_2),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f70,f44])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f28])).
% 0.22/0.55  fof(f214,plain,(
% 0.22/0.55    spl7_13 | ~spl7_3 | ~spl7_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f193,f80,f74,f211])).
% 0.22/0.55  fof(f80,plain,(
% 0.22/0.55    spl7_4 <=> r2_hidden(sK5(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.55  fof(f193,plain,(
% 0.22/0.55    r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),k2_relat_1(sK1)) | (~spl7_3 | ~spl7_4)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f76,f82,f50])).
% 0.22/0.55  fof(f50,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),k2_relat_1(X2)) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    r2_hidden(sK5(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) | ~spl7_4),
% 0.22/0.55    inference(avatar_component_clause,[],[f80])).
% 0.22/0.55  fof(f209,plain,(
% 0.22/0.55    spl7_12 | ~spl7_3 | ~spl7_4),
% 0.22/0.55    inference(avatar_split_clause,[],[f194,f80,f74,f206])).
% 0.22/0.55  fof(f194,plain,(
% 0.22/0.55    r2_hidden(sK4(sK5(k10_relat_1(sK1,sK0)),sK0,sK1),sK0) | (~spl7_3 | ~spl7_4)),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f76,f82,f52])).
% 0.22/0.55  fof(f52,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK4(X0,X1,X2),X1)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f34])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    spl7_4 | spl7_1),
% 0.22/0.55    inference(avatar_split_clause,[],[f78,f64,f80])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    r2_hidden(sK5(k10_relat_1(sK1,sK0)),k10_relat_1(sK1,sK0)) | spl7_1),
% 0.22/0.55    inference(unit_resulting_resolution,[],[f66,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.55    inference(cnf_transformation,[],[f36])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f21,f35])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl7_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f64])).
% 0.22/0.55  fof(f77,plain,(
% 0.22/0.55    spl7_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f41,f74])).
% 0.22/0.55  fof(f41,plain,(
% 0.22/0.55    v1_relat_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    (~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f25])).
% 0.22/0.55  % (10177)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)) & (r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ? [X0,X1] : ((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.22/0.55    inference(flattening,[],[f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    ? [X0,X1] : (((~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.22/0.55    inference(nnf_transformation,[],[f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.55    inference(ennf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.55    inference(negated_conjecture,[],[f10])).
% 0.22/0.55  fof(f10,conjecture,(
% 0.22/0.55    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.22/0.55  fof(f72,plain,(
% 0.22/0.55    spl7_1 | spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f42,f68,f64])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    ~spl7_1 | ~spl7_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f43,f68,f64])).
% 0.22/0.55  fof(f43,plain,(
% 0.22/0.55    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f26])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (10161)------------------------------
% 0.22/0.55  % (10161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (10161)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (10161)Memory used [KB]: 11129
% 0.22/0.55  % (10161)Time elapsed: 0.111 s
% 0.22/0.55  % (10161)------------------------------
% 0.22/0.55  % (10161)------------------------------
% 0.22/0.55  % (10164)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.55  % (10171)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.55  % (10160)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.56  % (10154)Success in time 0.19 s
%------------------------------------------------------------------------------
