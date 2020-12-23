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
% DateTime   : Thu Dec  3 13:00:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 341 expanded)
%              Number of leaves         :   36 ( 140 expanded)
%              Depth                    :   16
%              Number of atoms          :  609 (1267 expanded)
%              Number of equality atoms :   89 ( 184 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f358,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f118,f124,f131,f138,f179,f189,f210,f226,f236,f239,f241,f245,f247,f324,f334,f339,f344,f357])).

fof(f357,plain,
    ( ~ spl4_15
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f355,f205,f167])).

fof(f167,plain,
    ( spl4_15
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

% (15783)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f205,plain,
    ( spl4_18
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f355,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl4_18 ),
    inference(resolution,[],[f206,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f206,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f205])).

fof(f344,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | ~ spl4_13
    | spl4_15 ),
    inference(avatar_split_clause,[],[f254,f167,f158,f80,f84])).

fof(f84,plain,
    ( spl4_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f80,plain,
    ( spl4_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f158,plain,
    ( spl4_13
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f254,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_15 ),
    inference(resolution,[],[f168,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f168,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f167])).

fof(f339,plain,
    ( ~ spl4_16
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f337,f319,f175])).

fof(f175,plain,
    ( spl4_16
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f319,plain,
    ( spl4_36
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f337,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl4_36 ),
    inference(resolution,[],[f320,f63])).

fof(f320,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f319])).

fof(f334,plain,
    ( ~ spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_2
    | spl4_37 ),
    inference(avatar_split_clause,[],[f326,f322,f76,f84,f80,f161])).

fof(f161,plain,
    ( spl4_14
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f76,plain,
    ( spl4_2
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f322,plain,
    ( spl4_37
  <=> r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f326,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_ordinal1(sK1,sK0)
    | spl4_37 ),
    inference(superposition,[],[f323,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(resolution,[],[f61,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f323,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | spl4_37 ),
    inference(avatar_component_clause,[],[f322])).

fof(f324,plain,
    ( spl4_36
    | ~ spl4_4
    | spl4_1
    | ~ spl4_37
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f317,f243,f84,f80,f322,f72,f84,f319])).

fof(f72,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f243,plain,
    ( spl4_25
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f317,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f315,f244])).

fof(f244,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f243])).

fof(f315,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),sK1)))
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | r2_hidden(sK0,sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f199,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f51,f81])).

fof(f81,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f199,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK0)
        | ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f196,f85])).

fof(f85,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(global_subsumption,[],[f46,f195])).

fof(f195,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f194,f89])).

fof(f89,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f46,f70])).

fof(f70,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f47,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f46,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f247,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_14
    | spl4_16 ),
    inference(avatar_split_clause,[],[f180,f175,f161,f84,f80])).

fof(f180,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl4_16 ),
    inference(resolution,[],[f176,f61])).

fof(f176,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f245,plain,
    ( spl4_1
    | ~ spl4_14
    | spl4_25
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f192,f136,f80,f243,f161,f72])).

fof(f136,plain,
    ( spl4_10
  <=> ! [X0] :
        ( ~ r1_ordinal1(X0,sK0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | ~ v3_ordinal1(X0)
        | sK0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f192,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ r1_ordinal1(sK1,sK0)
    | sK0 = sK1
    | ~ spl4_3
    | ~ spl4_10 ),
    inference(resolution,[],[f137,f81])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | ~ r1_ordinal1(X0,sK0)
        | sK0 = X0 )
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f241,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_21 ),
    inference(resolution,[],[f218,f46])).

fof(f218,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl4_21
  <=> v1_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f239,plain,
    ( ~ spl4_24
    | ~ spl4_21
    | ~ spl4_2
    | spl4_23 ),
    inference(avatar_split_clause,[],[f237,f224,f76,f217,f229])).

fof(f229,plain,
    ( spl4_24
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f224,plain,
    ( spl4_23
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f237,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_23 ),
    inference(resolution,[],[f225,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f225,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f224])).

fof(f236,plain,(
    spl4_24 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl4_24 ),
    inference(resolution,[],[f230,f46])).

fof(f230,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f229])).

fof(f226,plain,
    ( ~ spl4_13
    | ~ spl4_4
    | ~ spl4_3
    | ~ spl4_23
    | spl4_19 ),
    inference(avatar_split_clause,[],[f212,f208,f224,f80,f84,f158])).

fof(f208,plain,
    ( spl4_19
  <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f212,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r1_ordinal1(sK0,sK1)
    | spl4_19 ),
    inference(superposition,[],[f209,f92])).

fof(f209,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f208])).

fof(f210,plain,
    ( spl4_18
    | ~ spl4_3
    | spl4_1
    | ~ spl4_19
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f203,f187,f84,f80,f208,f72,f80,f205])).

fof(f187,plain,
    ( spl4_17
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f203,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f202,f188])).

fof(f188,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f202,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK0)))
    | sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | r2_hidden(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f198,f94])).

fof(f94,plain,
    ( ! [X1] :
        ( r2_hidden(sK0,X1)
        | sK0 = X1
        | ~ v3_ordinal1(X1)
        | r2_hidden(X1,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f51,f85])).

fof(f198,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) )
    | ~ spl4_3 ),
    inference(resolution,[],[f196,f81])).

fof(f189,plain,
    ( spl4_1
    | ~ spl4_13
    | spl4_17
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f185,f129,f84,f187,f158,f72])).

fof(f129,plain,
    ( spl4_9
  <=> ! [X0] :
        ( ~ r1_ordinal1(X0,sK1)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | ~ v3_ordinal1(X0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f185,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ r1_ordinal1(sK0,sK1)
    | sK0 = sK1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f130,f85])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | ~ r1_ordinal1(X0,sK1)
        | sK1 = X0 )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f129])).

fof(f179,plain,
    ( ~ spl4_4
    | ~ spl4_3
    | spl4_13
    | spl4_14 ),
    inference(avatar_split_clause,[],[f173,f161,f158,f80,f84])).

fof(f173,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_14 ),
    inference(resolution,[],[f162,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f162,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f138,plain,
    ( ~ spl4_4
    | spl4_10
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f134,f122,f136,f84])).

fof(f122,plain,
    ( spl4_8
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(X0,sK0)
        | sK0 = X0
        | r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(X0,sK0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | ~ v3_ordinal1(sK0) )
    | ~ spl4_8 ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(X0,sK0)
        | sK0 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK0),X0) = X0
        | ~ v3_ordinal1(sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl4_8 ),
    inference(resolution,[],[f123,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f123,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r1_ordinal1(X0,sK0)
        | sK0 = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f131,plain,
    ( ~ spl4_3
    | spl4_9
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f127,f116,f129,f80])).

fof(f116,plain,
    ( spl4_7
  <=> ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(X0,sK1)
        | sK1 = X0
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(X0,sK1)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | ~ v3_ordinal1(sK1) )
    | ~ spl4_7 ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_ordinal1(X0,sK1)
        | sK1 = X0
        | ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X0) )
    | ~ spl4_7 ),
    inference(resolution,[],[f117,f50])).

fof(f117,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r1_ordinal1(X0,sK1)
        | sK1 = X0
        | ~ v3_ordinal1(X0) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f124,plain,
    ( ~ spl4_4
    | spl4_8
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f120,f84,f122,f84])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK0)
        | sK0 = X0
        | ~ r1_ordinal1(X0,sK0)
        | ~ v3_ordinal1(sK0) )
    | ~ spl4_4 ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK0)
        | sK0 = X0
        | ~ r1_ordinal1(X0,sK0)
        | ~ v3_ordinal1(sK0)
        | ~ v3_ordinal1(X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f105,f61])).

fof(f105,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK0)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X1,sK0)
        | sK0 = X1 )
    | ~ spl4_4 ),
    inference(resolution,[],[f94,f63])).

fof(f118,plain,
    ( ~ spl4_3
    | spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f114,f80,f116,f80])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK1)
        | sK1 = X0
        | ~ r1_ordinal1(X0,sK1)
        | ~ v3_ordinal1(sK1) )
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | r2_hidden(X0,sK1)
        | sK1 = X0
        | ~ r1_ordinal1(X0,sK1)
        | ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f96,f61])).

fof(f96,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ v3_ordinal1(X1)
        | r2_hidden(X1,sK1)
        | sK1 = X1 )
    | ~ spl4_3 ),
    inference(resolution,[],[f93,f63])).

fof(f86,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f82,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f43,f80])).

fof(f43,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f44,f76])).

fof(f44,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f45,f72])).

fof(f45,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:52:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (15786)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (15794)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (15794)Refutation not found, incomplete strategy% (15794)------------------------------
% 0.22/0.47  % (15794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (15794)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (15794)Memory used [KB]: 1663
% 0.22/0.47  % (15794)Time elapsed: 0.057 s
% 0.22/0.47  % (15794)------------------------------
% 0.22/0.47  % (15794)------------------------------
% 0.22/0.47  % (15788)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (15789)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (15787)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (15797)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (15796)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (15795)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (15796)Refutation not found, incomplete strategy% (15796)------------------------------
% 0.22/0.49  % (15796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (15796)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (15796)Memory used [KB]: 6268
% 0.22/0.49  % (15796)Time elapsed: 0.004 s
% 0.22/0.49  % (15796)------------------------------
% 0.22/0.49  % (15796)------------------------------
% 0.22/0.50  % (15787)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f358,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f118,f124,f131,f138,f179,f189,f210,f226,f236,f239,f241,f245,f247,f324,f334,f339,f344,f357])).
% 0.22/0.50  fof(f357,plain,(
% 0.22/0.50    ~spl4_15 | ~spl4_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f355,f205,f167])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    spl4_15 <=> r1_tarski(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.50  % (15783)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl4_18 <=> r2_hidden(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.50  fof(f355,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | ~spl4_18),
% 0.22/0.50    inference(resolution,[],[f206,f63])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | ~spl4_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    ~spl4_4 | ~spl4_3 | ~spl4_13 | spl4_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f254,f167,f158,f80,f84])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    spl4_4 <=> v3_ordinal1(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl4_3 <=> v3_ordinal1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl4_13 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.50  fof(f254,plain,(
% 0.22/0.50    ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_15),
% 0.22/0.50    inference(resolution,[],[f168,f61])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ~r1_tarski(sK0,sK1) | spl4_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f167])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    ~spl4_16 | ~spl4_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f337,f319,f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl4_16 <=> r1_tarski(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.50  fof(f319,plain,(
% 0.22/0.50    spl4_36 <=> r2_hidden(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK0) | ~spl4_36),
% 0.22/0.50    inference(resolution,[],[f320,f63])).
% 0.22/0.50  fof(f320,plain,(
% 0.22/0.50    r2_hidden(sK0,sK1) | ~spl4_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f319])).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    ~spl4_14 | ~spl4_3 | ~spl4_4 | ~spl4_2 | spl4_37),
% 0.22/0.50    inference(avatar_split_clause,[],[f326,f322,f76,f84,f80,f161])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl4_14 <=> r1_ordinal1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl4_2 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    spl4_37 <=> r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~r1_ordinal1(sK1,sK0) | spl4_37),
% 0.22/0.50    inference(superposition,[],[f323,f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,X1)) )),
% 0.22/0.50    inference(resolution,[],[f61,f59])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.50  fof(f323,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | spl4_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f322])).
% 0.22/0.50  fof(f324,plain,(
% 0.22/0.50    spl4_36 | ~spl4_4 | spl4_1 | ~spl4_37 | ~spl4_3 | ~spl4_4 | ~spl4_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f317,f243,f84,f80,f322,f72,f84,f319])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    spl4_1 <=> sK0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.50  fof(f243,plain,(
% 0.22/0.50    spl4_25 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | sK0 = sK1 | ~v3_ordinal1(sK0) | r2_hidden(sK0,sK1) | (~spl4_3 | ~spl4_4 | ~spl4_25)),
% 0.22/0.50    inference(forward_demodulation,[],[f315,f244])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl4_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f243])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),sK1))) | sK0 = sK1 | ~v3_ordinal1(sK0) | r2_hidden(sK0,sK1) | (~spl4_3 | ~spl4_4)),
% 0.22/0.50    inference(resolution,[],[f199,f93])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0) | r2_hidden(X0,sK1)) ) | ~spl4_3),
% 0.22/0.50    inference(resolution,[],[f51,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    v3_ordinal1(sK1) | ~spl4_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.50  fof(f199,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,sK0) | ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1)))) ) | ~spl4_4),
% 0.22/0.50    inference(resolution,[],[f196,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    v3_ordinal1(sK0) | ~spl4_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f84])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1)) )),
% 0.22/0.50    inference(global_subsumption,[],[f46,f195])).
% 0.22/0.50  fof(f195,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.50    inference(forward_demodulation,[],[f194,f89])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.50    inference(global_subsumption,[],[f46,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.50    inference(equality_resolution,[],[f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f38,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(rectify,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.50    inference(resolution,[],[f47,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    ~spl4_3 | ~spl4_4 | ~spl4_14 | spl4_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f180,f175,f161,f84,f80])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl4_16),
% 0.22/0.50    inference(resolution,[],[f176,f61])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ~r1_tarski(sK1,sK0) | spl4_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f175])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    spl4_1 | ~spl4_14 | spl4_25 | ~spl4_3 | ~spl4_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f192,f136,f80,f243,f161,f72])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    spl4_10 <=> ! [X0] : (~r1_ordinal1(X0,sK0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~v3_ordinal1(X0) | sK0 = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.50  fof(f192,plain,(
% 0.22/0.50    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~r1_ordinal1(sK1,sK0) | sK0 = sK1 | (~spl4_3 | ~spl4_10)),
% 0.22/0.50    inference(resolution,[],[f137,f81])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~r1_ordinal1(X0,sK0) | sK0 = X0) ) | ~spl4_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f136])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    spl4_21),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f240])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    $false | spl4_21),
% 0.22/0.50    inference(resolution,[],[f218,f46])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    ~v1_relat_1(k1_wellord2(sK1)) | spl4_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl4_21 <=> v1_relat_1(k1_wellord2(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ~spl4_24 | ~spl4_21 | ~spl4_2 | spl4_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f237,f224,f76,f217,f229])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    spl4_24 <=> v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    spl4_23 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | spl4_23),
% 0.22/0.50    inference(resolution,[],[f225,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | spl4_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f224])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    spl4_24),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    $false | spl4_24),
% 0.22/0.50    inference(resolution,[],[f230,f46])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    ~v1_relat_1(k1_wellord2(sK0)) | spl4_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f229])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ~spl4_13 | ~spl4_4 | ~spl4_3 | ~spl4_23 | spl4_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f212,f208,f224,f80,f84,f158])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    spl4_19 <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r1_ordinal1(sK0,sK1) | spl4_19),
% 0.22/0.50    inference(superposition,[],[f209,f92])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | spl4_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f208])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl4_18 | ~spl4_3 | spl4_1 | ~spl4_19 | ~spl4_3 | ~spl4_4 | ~spl4_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f203,f187,f84,f80,f208,f72,f80,f205])).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    spl4_17 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | sK0 = sK1 | ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0) | (~spl4_3 | ~spl4_4 | ~spl4_17)),
% 0.22/0.50    inference(forward_demodulation,[],[f202,f188])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl4_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f187])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK0))) | sK0 = sK1 | ~v3_ordinal1(sK1) | r2_hidden(sK1,sK0) | (~spl4_3 | ~spl4_4)),
% 0.22/0.50    inference(resolution,[],[f198,f94])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(sK0,X1) | sK0 = X1 | ~v3_ordinal1(X1) | r2_hidden(X1,sK0)) ) | ~spl4_4),
% 0.22/0.50    inference(resolution,[],[f51,f85])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))) ) | ~spl4_3),
% 0.22/0.50    inference(resolution,[],[f196,f81])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    spl4_1 | ~spl4_13 | spl4_17 | ~spl4_4 | ~spl4_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f185,f129,f84,f187,f158,f72])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl4_9 <=> ! [X0] : (~r1_ordinal1(X0,sK1) | k1_wellord1(k1_wellord2(sK1),X0) = X0 | ~v3_ordinal1(X0) | sK1 = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~r1_ordinal1(sK0,sK1) | sK0 = sK1 | (~spl4_4 | ~spl4_9)),
% 0.22/0.50    inference(resolution,[],[f130,f85])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0 | ~r1_ordinal1(X0,sK1) | sK1 = X0) ) | ~spl4_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f129])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ~spl4_4 | ~spl4_3 | spl4_13 | spl4_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f173,f161,f158,f80,f84])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_14),
% 0.22/0.50    inference(resolution,[],[f162,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~r1_ordinal1(sK1,sK0) | spl4_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~spl4_4 | spl4_10 | ~spl4_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f134,f122,f136,f84])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    spl4_8 <=> ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(X0,sK0) | sK0 = X0 | r2_hidden(X0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_ordinal1(X0,sK0) | sK0 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~v3_ordinal1(sK0)) ) | ~spl4_8),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f132])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_ordinal1(X0,sK0) | sK0 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK0),X0) = X0 | ~v3_ordinal1(sK0) | ~v3_ordinal1(X0)) ) | ~spl4_8),
% 0.22/0.50    inference(resolution,[],[f123,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,sK0) | ~r1_ordinal1(X0,sK0) | sK0 = X0 | ~v3_ordinal1(X0)) ) | ~spl4_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f122])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ~spl4_3 | spl4_9 | ~spl4_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f127,f116,f129,f80])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl4_7 <=> ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(X0,sK1) | sK1 = X0 | r2_hidden(X0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_ordinal1(X0,sK1) | sK1 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0 | ~v3_ordinal1(sK1)) ) | ~spl4_7),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X0] : (~r1_ordinal1(X0,sK1) | sK1 = X0 | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0 | ~v3_ordinal1(sK1) | ~v3_ordinal1(X0)) ) | ~spl4_7),
% 0.22/0.50    inference(resolution,[],[f117,f50])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~r1_ordinal1(X0,sK1) | sK1 = X0 | ~v3_ordinal1(X0)) ) | ~spl4_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~spl4_4 | spl4_8 | ~spl4_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f120,f84,f122,f84])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK0) | sK0 = X0 | ~r1_ordinal1(X0,sK0) | ~v3_ordinal1(sK0)) ) | ~spl4_4),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f119])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK0) | sK0 = X0 | ~r1_ordinal1(X0,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(X0)) ) | ~spl4_4),
% 0.22/0.50    inference(resolution,[],[f105,f61])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(X1,sK0) | ~v3_ordinal1(X1) | r2_hidden(X1,sK0) | sK0 = X1) ) | ~spl4_4),
% 0.22/0.50    inference(resolution,[],[f94,f63])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~spl4_3 | spl4_7 | ~spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f114,f80,f116,f80])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK1) | sK1 = X0 | ~r1_ordinal1(X0,sK1) | ~v3_ordinal1(sK1)) ) | ~spl4_3),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f113])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(X0,sK1) | sK1 = X0 | ~r1_ordinal1(X0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(X0)) ) | ~spl4_3),
% 0.22/0.50    inference(resolution,[],[f96,f61])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(X1,sK1) | ~v3_ordinal1(X1) | r2_hidden(X1,sK1) | sK1 = X1) ) | ~spl4_3),
% 0.22/0.50    inference(resolution,[],[f93,f63])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    spl4_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f42,f84])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    v3_ordinal1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f34,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f12])).
% 0.22/0.50  fof(f12,conjecture,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    spl4_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f43,f80])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    v3_ordinal1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl4_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f44,f76])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ~spl4_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f45,f72])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    sK0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15787)------------------------------
% 0.22/0.50  % (15787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15787)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15787)Memory used [KB]: 10874
% 0.22/0.50  % (15787)Time elapsed: 0.057 s
% 0.22/0.50  % (15787)------------------------------
% 0.22/0.50  % (15787)------------------------------
% 0.22/0.50  % (15780)Success in time 0.136 s
%------------------------------------------------------------------------------
