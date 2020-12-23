%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 147 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  293 ( 449 expanded)
%              Number of equality atoms :   80 ( 132 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f227,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f84,f89,f95,f136,f151,f226])).

fof(f226,plain,
    ( ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f222,f149,f67])).

fof(f67,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f149,plain,
    ( spl4_10
  <=> r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f222,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f174,f56])).

fof(f56,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f37])).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f174,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_tarski(X0,X0),k2_tarski(sK0,sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl4_10 ),
    inference(resolution,[],[f164,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f45,f37])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK0,sK0))
        | ~ r2_hidden(X0,k1_relat_1(sK1)) )
    | ~ spl4_10 ),
    inference(resolution,[],[f150,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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

% (1304)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f150,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f149])).

fof(f151,plain,
    ( spl4_10
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f147,f134,f82,f149])).

fof(f82,plain,
    ( spl4_5
  <=> ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( spl4_9
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f147,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f137])).

fof(f137,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(superposition,[],[f83,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f83,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0)) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f82])).

% (1288)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f136,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f132,f93,f63,f134])).

fof(f63,plain,
    ( spl4_1
  <=> k11_relat_1(sK1,sK0) = k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f93,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X1,k11_relat_1(sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f132,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | spl4_1
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f126])).

fof(f126,plain,
    ( k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0)
    | k1_xboole_0 = k11_relat_1(sK1,sK0)
    | spl4_1
    | ~ spl4_7 ),
    inference(superposition,[],[f64,f125])).

fof(f125,plain,
    ( ! [X0] :
        ( k11_relat_1(sK1,X0) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0))
        | k1_xboole_0 = k11_relat_1(sK1,X0) )
    | ~ spl4_7 ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != X3
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k2_tarski(X3,X3) = k11_relat_1(sK1,X2) )
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != X3
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k2_tarski(X3,X3) = k11_relat_1(sK1,X2)
        | k1_xboole_0 = k11_relat_1(sK1,X2)
        | k2_tarski(X3,X3) = k11_relat_1(sK1,X2) )
    | ~ spl4_7 ),
    inference(superposition,[],[f59,f101])).

fof(f101,plain,
    ( ! [X12,X11] :
        ( k1_funct_1(sK1,X11) = sK3(k11_relat_1(sK1,X11),X12)
        | k1_xboole_0 = k11_relat_1(sK1,X11)
        | k11_relat_1(sK1,X11) = k2_tarski(X12,X12) )
    | ~ spl4_7 ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK3(X0,X1) != X1
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_tarski(X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f48,f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,
    ( k11_relat_1(sK1,sK0) != k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f95,plain,
    ( ~ spl4_4
    | spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f90,f87,f93,f75])).

fof(f75,plain,
    ( spl4_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f87,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK1,X0) = X1
        | ~ r2_hidden(X1,k11_relat_1(sK1,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_6 ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f89,plain,
    ( ~ spl4_4
    | spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f85,f71,f87,f75])).

fof(f71,plain,
    ( spl4_3
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | k1_funct_1(sK1,X0) = X1
        | ~ v1_relat_1(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,
    ( v1_funct_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f84,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f79,f75,f82,f75])).

fof(f79,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0))
        | ~ v1_relat_1(sK1) )
    | ~ spl4_4 ),
    inference(superposition,[],[f43,f78])).

fof(f78,plain,
    ( ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_tarski(X0,X0))
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f76])).

fof(f76,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f38,f37])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f77,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f33,f75])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
    & r2_hidden(sK0,k1_relat_1(sK1))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).

fof(f22,plain,
    ( ? [X0,X1] :
        ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
        & r2_hidden(X0,k1_relat_1(X1))
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))
      & r2_hidden(sK0,k1_relat_1(sK1))
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0))
      & r2_hidden(X0,k1_relat_1(X1))
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( r2_hidden(X0,k1_relat_1(X1))
         => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).

fof(f73,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f34,f71])).

fof(f34,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f69,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f54,f63])).

fof(f54,plain,(
    k11_relat_1(sK1,sK0) != k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f23])).

% (1306)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (1293)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (1284)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (1281)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (1307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (1287)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (1299)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (1303)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (1280)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (1295)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (1302)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (1294)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (1291)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (1285)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (1282)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (1299)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (1282)Refutation not found, incomplete strategy% (1282)------------------------------
% 0.21/0.53  % (1282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1282)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1282)Memory used [KB]: 10746
% 0.21/0.53  % (1282)Time elapsed: 0.124 s
% 0.21/0.53  % (1282)------------------------------
% 0.21/0.53  % (1282)------------------------------
% 0.21/0.53  % (1302)Refutation not found, incomplete strategy% (1302)------------------------------
% 0.21/0.53  % (1302)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (1302)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (1302)Memory used [KB]: 10746
% 0.21/0.53  % (1302)Time elapsed: 0.093 s
% 0.21/0.53  % (1302)------------------------------
% 0.21/0.53  % (1302)------------------------------
% 0.21/0.53  % (1305)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.53  % (1300)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (1308)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (1283)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f227,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f65,f69,f73,f77,f84,f89,f95,f136,f151,f226])).
% 0.21/0.54  fof(f226,plain,(
% 0.21/0.54    ~spl4_2 | ~spl4_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f222,f149,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl4_2 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    spl4_10 <=> r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK1)) | ~spl4_10),
% 0.21/0.54    inference(resolution,[],[f174,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f39,f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    ( ! [X0] : (~r1_tarski(k2_tarski(X0,X0),k2_tarski(sK0,sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl4_10),
% 0.21/0.54    inference(resolution,[],[f164,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_tarski(X0,X0),X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f45,f37])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK0,sK0)) | ~r2_hidden(X0,k1_relat_1(sK1))) ) | ~spl4_10),
% 0.21/0.54    inference(resolution,[],[f150,f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  % (1304)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | ~spl4_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f149])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    spl4_10 | ~spl4_5 | ~spl4_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f147,f134,f82,f149])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl4_5 <=> ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl4_9 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | (~spl4_5 | ~spl4_9)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | (~spl4_5 | ~spl4_9)),
% 0.21/0.54    inference(superposition,[],[f83,f135])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl4_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f134])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0))) ) | ~spl4_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  % (1288)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl4_9 | spl4_1 | ~spl4_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f132,f93,f63,f134])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl4_1 <=> k11_relat_1(sK1,sK0) = k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    spl4_7 <=> ! [X1,X0] : (k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X1,k11_relat_1(sK1,X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | (spl4_1 | ~spl4_7)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f126])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    k11_relat_1(sK1,sK0) != k11_relat_1(sK1,sK0) | k1_xboole_0 = k11_relat_1(sK1,sK0) | (spl4_1 | ~spl4_7)),
% 0.21/0.54    inference(superposition,[],[f64,f125])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k2_tarski(k1_funct_1(sK1,X0),k1_funct_1(sK1,X0)) | k1_xboole_0 = k11_relat_1(sK1,X0)) ) | ~spl4_7),
% 0.21/0.54    inference(equality_resolution,[],[f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != X3 | k1_xboole_0 = k11_relat_1(sK1,X2) | k2_tarski(X3,X3) = k11_relat_1(sK1,X2)) ) | ~spl4_7),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f122])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != X3 | k1_xboole_0 = k11_relat_1(sK1,X2) | k2_tarski(X3,X3) = k11_relat_1(sK1,X2) | k1_xboole_0 = k11_relat_1(sK1,X2) | k2_tarski(X3,X3) = k11_relat_1(sK1,X2)) ) | ~spl4_7),
% 0.21/0.54    inference(superposition,[],[f59,f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    ( ! [X12,X11] : (k1_funct_1(sK1,X11) = sK3(k11_relat_1(sK1,X11),X12) | k1_xboole_0 = k11_relat_1(sK1,X11) | k11_relat_1(sK1,X11) = k2_tarski(X12,X12)) ) | ~spl4_7),
% 0.21/0.54    inference(resolution,[],[f94,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f47,f37])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : ((sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) => (sK3(X0,X1) != X1 & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) ) | ~spl4_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f93])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k2_tarski(X1,X1) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f48,f37])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    k11_relat_1(sK1,sK0) != k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) | spl4_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ~spl4_4 | spl4_7 | ~spl4_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f90,f87,f93,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    spl4_4 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    spl4_6 <=> ! [X1,X0] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_funct_1(sK1,X0) = X1 | ~r2_hidden(X1,k11_relat_1(sK1,X0)) | ~v1_relat_1(sK1)) ) | ~spl4_6),
% 0.21/0.54    inference(resolution,[],[f88,f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1) ) | ~spl4_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f87])).
% 0.21/0.54  fof(f89,plain,(
% 0.21/0.54    ~spl4_4 | spl4_6 | ~spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f85,f71,f87,f75])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    spl4_3 <=> v1_funct_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | k1_funct_1(sK1,X0) = X1 | ~v1_relat_1(sK1)) ) | ~spl4_3),
% 0.21/0.54    inference(resolution,[],[f52,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    v1_funct_1(sK1) | ~spl4_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f71])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ~spl4_4 | spl4_5 | ~spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f79,f75,f82,f75])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),k2_tarski(X0,X0)) | ~v1_relat_1(sK1)) ) | ~spl4_4),
% 0.21/0.54    inference(superposition,[],[f43,f78])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_tarski(X0,X0))) ) | ~spl4_4),
% 0.21/0.54    inference(resolution,[],[f55,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl4_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f75])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f38,f37])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl4_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f75])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1)) => (k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0)) & r2_hidden(sK0,k1_relat_1(sK1)) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1] : (k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1)) & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1] : ((k11_relat_1(X1,X0) != k1_tarski(k1_funct_1(X1,X0)) & r2_hidden(X0,k1_relat_1(X1))) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k11_relat_1(X1,X0) = k1_tarski(k1_funct_1(X1,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_funct_1)).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    spl4_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f34,f71])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    v1_funct_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl4_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f67])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~spl4_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f54,f63])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    k11_relat_1(sK1,sK0) != k2_tarski(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 0.21/0.54    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    k11_relat_1(sK1,sK0) != k1_tarski(k1_funct_1(sK1,sK0))),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  % (1306)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (1299)------------------------------
% 0.21/0.54  % (1299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1299)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (1299)Memory used [KB]: 10874
% 0.21/0.54  % (1299)Time elapsed: 0.119 s
% 0.21/0.54  % (1299)------------------------------
% 0.21/0.54  % (1299)------------------------------
% 0.21/0.54  % (1288)Refutation not found, incomplete strategy% (1288)------------------------------
% 0.21/0.54  % (1288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1288)Memory used [KB]: 10746
% 0.21/0.54  % (1288)Time elapsed: 0.135 s
% 0.21/0.54  % (1288)------------------------------
% 0.21/0.54  % (1288)------------------------------
% 0.21/0.54  % (1289)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1286)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (1279)Success in time 0.184 s
%------------------------------------------------------------------------------
