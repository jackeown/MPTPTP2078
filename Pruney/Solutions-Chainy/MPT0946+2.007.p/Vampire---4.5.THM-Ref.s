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
% Statistics : Number of formulae       :  166 ( 397 expanded)
%              Number of leaves         :   37 ( 153 expanded)
%              Depth                    :   17
%              Number of atoms          :  675 (1757 expanded)
%              Number of equality atoms :  111 ( 348 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f122,f140,f153,f157,f196,f230,f241,f257,f289,f292,f326,f337,f385,f399,f400,f405,f414,f422])).

fof(f422,plain,
    ( ~ spl5_30
    | ~ spl5_9
    | ~ spl5_2
    | spl5_43 ),
    inference(avatar_split_clause,[],[f421,f412,f95,f144,f284])).

fof(f284,plain,
    ( spl5_30
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f144,plain,
    ( spl5_9
  <=> v1_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f95,plain,
    ( spl5_2
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f412,plain,
    ( spl5_43
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f421,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_43 ),
    inference(resolution,[],[f413,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f413,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f412])).

fof(f414,plain,
    ( ~ spl5_43
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f410,f191,f170,f138,f99,f412])).

fof(f99,plain,
    ( spl5_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f138,plain,
    ( spl5_8
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f170,plain,
    ( spl5_14
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f191,plain,
    ( spl5_18
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f410,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f409,f192])).

fof(f192,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f191])).

fof(f409,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ spl5_3
    | ~ spl5_8
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f406,f139])).

fof(f139,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f406,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK0)))
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(resolution,[],[f171,f374])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) )
    | ~ spl5_3 ),
    inference(resolution,[],[f209,f100])).

fof(f100,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f209,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(global_subsumption,[],[f54,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f207,f109])).

fof(f109,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f54,f89])).

fof(f89,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f55,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f54,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f171,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f405,plain,
    ( spl5_1
    | ~ spl5_4
    | spl5_7
    | ~ spl5_3
    | spl5_11
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f347,f287,f151,f99,f134,f103,f91])).

fof(f91,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f103,plain,
    ( spl5_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f134,plain,
    ( spl5_7
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f151,plain,
    ( spl5_11
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f287,plain,
    ( spl5_31
  <=> ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f347,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | ~ spl5_3
    | spl5_11
    | ~ spl5_31 ),
    inference(resolution,[],[f339,f152])).

fof(f152,plain,
    ( ~ r2_hidden(sK0,sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f339,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | sK1 = X0 )
    | ~ spl5_3
    | ~ spl5_31 ),
    inference(resolution,[],[f288,f113])).

fof(f113,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | sK1 = X0 )
    | ~ spl5_3 ),
    inference(resolution,[],[f65,f100])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK0) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f287])).

fof(f400,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_15
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f327,f134,f173,f103,f99])).

fof(f173,plain,
    ( spl5_15
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f327,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f135,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f135,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f134])).

fof(f399,plain,
    ( ~ spl5_7
    | ~ spl5_23
    | spl5_35 ),
    inference(avatar_split_clause,[],[f398,f335,f228,f134])).

fof(f228,plain,
    ( spl5_23
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f335,plain,
    ( spl5_35
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f398,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl5_23
    | spl5_35 ),
    inference(resolution,[],[f229,f336])).

fof(f336,plain,
    ( ~ r2_hidden(sK1,sK1)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f335])).

fof(f229,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f228])).

fof(f385,plain,
    ( ~ spl5_7
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_15
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f383,f238,f173,f103,f95,f134])).

fof(f238,plain,
    ( spl5_24
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f383,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_15
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f378,f239])).

fof(f239,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f238])).

fof(f378,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(superposition,[],[f375,f174])).

fof(f174,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f375,plain,
    ( ! [X1] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1)))
        | ~ r2_hidden(X1,sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f209,f104])).

fof(f104,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f337,plain,
    ( ~ spl5_30
    | ~ spl5_35
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f329,f173,f335,f284])).

fof(f329,plain,
    ( ~ r2_hidden(sK1,sK1)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_15 ),
    inference(superposition,[],[f82,f174])).

fof(f82,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                | sK2(X0,X1,X2) = X1
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                  & sK2(X0,X1,X2) != X1 )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
          | sK2(X0,X1,X2) = X1
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
            & sK2(X0,X1,X2) != X1 )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f326,plain,
    ( spl5_1
    | ~ spl5_4
    | spl5_7
    | ~ spl5_3
    | spl5_14 ),
    inference(avatar_split_clause,[],[f325,f170,f99,f134,f103,f91])).

fof(f325,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | sK0 = sK1
    | ~ spl5_3
    | spl5_14 ),
    inference(resolution,[],[f313,f113])).

fof(f313,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f292,plain,(
    spl5_30 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl5_30 ),
    inference(resolution,[],[f285,f54])).

fof(f285,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f284])).

fof(f289,plain,
    ( ~ spl5_30
    | spl5_31
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f282,f238,f287,f284])).

fof(f282,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f281,f109])).

fof(f281,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f279,f109])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl5_24 ),
    inference(superposition,[],[f77,f239])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f257,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | spl5_19
    | spl5_22 ),
    inference(avatar_split_clause,[],[f251,f217,f194,f99,f103])).

fof(f194,plain,
    ( spl5_19
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f217,plain,
    ( spl5_22
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f251,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl5_22 ),
    inference(resolution,[],[f240,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f240,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f241,plain,
    ( spl5_24
    | ~ spl5_22
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f235,f103,f99,f217,f238])).

fof(f235,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f180,f100])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | ~ r1_ordinal1(X1,sK0)
        | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f112,f104])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f230,plain,
    ( ~ spl5_9
    | spl5_23
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f226,f191,f228,f144])).

fof(f226,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK0)
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f225,f109])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | ~ spl5_18 ),
    inference(forward_demodulation,[],[f223,f109])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))
        | r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | ~ spl5_18 ),
    inference(superposition,[],[f77,f192])).

fof(f196,plain,
    ( spl5_18
    | ~ spl5_19
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f182,f103,f99,f194,f191])).

fof(f182,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(resolution,[],[f179,f104])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r1_ordinal1(X0,sK1)
        | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK1),X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f112,f100])).

fof(f157,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f145,f54])).

fof(f145,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f144])).

fof(f153,plain,
    ( ~ spl5_9
    | ~ spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f142,f138,f151,f144])).

fof(f142,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_8 ),
    inference(superposition,[],[f82,f139])).

fof(f140,plain,
    ( spl5_7
    | spl5_1
    | spl5_8
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f132,f120,f103,f138,f91,f134])).

fof(f120,plain,
    ( spl5_5
  <=> ! [X0] :
        ( r2_hidden(sK1,X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | sK1 = X0
        | ~ v3_ordinal1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f132,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(resolution,[],[f121,f104])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | sK1 = X0
        | r2_hidden(sK1,X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f122,plain,
    ( ~ spl5_3
    | spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f117,f99,f120,f99])).

fof(f117,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | sK1 = X0
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | ~ v3_ordinal1(sK1) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | sK1 = X0
        | k1_wellord1(k1_wellord2(sK1),X0) = X0
        | ~ v3_ordinal1(sK1)
        | ~ v3_ordinal1(X0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f113,f64])).

fof(f105,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f50,f103])).

fof(f50,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f101,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f52,f95])).

fof(f52,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f38])).

fof(f93,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f53,f91])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:43:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (4512)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (4520)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (4521)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (4513)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (4513)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (4520)Refutation not found, incomplete strategy% (4520)------------------------------
% 0.22/0.48  % (4520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (4520)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (4520)Memory used [KB]: 1663
% 0.22/0.48  % (4520)Time elapsed: 0.062 s
% 0.22/0.48  % (4520)------------------------------
% 0.22/0.48  % (4520)------------------------------
% 0.22/0.49  % (4516)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f423,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f93,f97,f101,f105,f122,f140,f153,f157,f196,f230,f241,f257,f289,f292,f326,f337,f385,f399,f400,f405,f414,f422])).
% 0.22/0.49  fof(f422,plain,(
% 0.22/0.49    ~spl5_30 | ~spl5_9 | ~spl5_2 | spl5_43),
% 0.22/0.49    inference(avatar_split_clause,[],[f421,f412,f95,f144,f284])).
% 0.22/0.49  fof(f284,plain,(
% 0.22/0.49    spl5_30 <=> v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    spl5_9 <=> v1_relat_1(k1_wellord2(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    spl5_2 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f412,plain,(
% 0.22/0.49    spl5_43 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.22/0.49  fof(f421,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_43),
% 0.22/0.49    inference(resolution,[],[f413,f56])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.49  fof(f413,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | spl5_43),
% 0.22/0.49    inference(avatar_component_clause,[],[f412])).
% 0.22/0.49  fof(f414,plain,(
% 0.22/0.49    ~spl5_43 | ~spl5_3 | ~spl5_8 | ~spl5_14 | ~spl5_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f410,f191,f170,f138,f99,f412])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl5_3 <=> v3_ordinal1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f138,plain,(
% 0.22/0.49    spl5_8 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl5_14 <=> r2_hidden(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    spl5_18 <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.49  fof(f410,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | (~spl5_3 | ~spl5_8 | ~spl5_14 | ~spl5_18)),
% 0.22/0.49    inference(forward_demodulation,[],[f409,f192])).
% 0.22/0.49  fof(f192,plain,(
% 0.22/0.49    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl5_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f191])).
% 0.22/0.49  fof(f409,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | (~spl5_3 | ~spl5_8 | ~spl5_14)),
% 0.22/0.49    inference(forward_demodulation,[],[f406,f139])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl5_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f138])).
% 0.22/0.49  fof(f406,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),sK0))) | (~spl5_3 | ~spl5_14)),
% 0.22/0.49    inference(resolution,[],[f171,f374])).
% 0.22/0.49  fof(f374,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))) ) | ~spl5_3),
% 0.22/0.49    inference(resolution,[],[f209,f100])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v3_ordinal1(sK1) | ~spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f99])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(global_subsumption,[],[f54,f208])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.49    inference(forward_demodulation,[],[f207,f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.49    inference(global_subsumption,[],[f54,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(rectify,[],[f45])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f44])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.49    inference(resolution,[],[f55,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    r2_hidden(sK0,sK1) | ~spl5_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f170])).
% 0.22/0.49  fof(f405,plain,(
% 0.22/0.49    spl5_1 | ~spl5_4 | spl5_7 | ~spl5_3 | spl5_11 | ~spl5_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f347,f287,f151,f99,f134,f103,f91])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl5_1 <=> sK0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    spl5_4 <=> v3_ordinal1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl5_7 <=> r2_hidden(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    spl5_11 <=> r2_hidden(sK0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.49  fof(f287,plain,(
% 0.22/0.49    spl5_31 <=> ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.49  fof(f347,plain,(
% 0.22/0.49    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | sK0 = sK1 | (~spl5_3 | spl5_11 | ~spl5_31)),
% 0.22/0.49    inference(resolution,[],[f339,f152])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ~r2_hidden(sK0,sK0) | spl5_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f151])).
% 0.22/0.49  fof(f339,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,sK0) | r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | sK1 = X0) ) | (~spl5_3 | ~spl5_31)),
% 0.22/0.49    inference(resolution,[],[f288,f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,sK1) | r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | sK1 = X0) ) | ~spl5_3),
% 0.22/0.49    inference(resolution,[],[f65,f100])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | r2_hidden(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.49  fof(f288,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) ) | ~spl5_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f287])).
% 0.22/0.49  fof(f400,plain,(
% 0.22/0.49    ~spl5_3 | ~spl5_4 | spl5_15 | ~spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f327,f134,f173,f103,f99])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    spl5_15 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.50  fof(f327,plain,(
% 0.22/0.50    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl5_7),
% 0.22/0.50    inference(resolution,[],[f135,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | ~spl5_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f134])).
% 0.22/0.50  fof(f399,plain,(
% 0.22/0.50    ~spl5_7 | ~spl5_23 | spl5_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f398,f335,f228,f134])).
% 0.22/0.50  fof(f228,plain,(
% 0.22/0.50    spl5_23 <=> ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    spl5_35 <=> r2_hidden(sK1,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.22/0.50  fof(f398,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK0) | (~spl5_23 | spl5_35)),
% 0.22/0.50    inference(resolution,[],[f229,f336])).
% 0.22/0.50  fof(f336,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK1) | spl5_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f335])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0)) ) | ~spl5_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f228])).
% 0.22/0.50  fof(f385,plain,(
% 0.22/0.50    ~spl5_7 | ~spl5_2 | ~spl5_4 | ~spl5_15 | ~spl5_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f383,f238,f173,f103,f95,f134])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl5_24 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.50  fof(f383,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,sK0) | (~spl5_4 | ~spl5_15 | ~spl5_24)),
% 0.22/0.50    inference(forward_demodulation,[],[f378,f239])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl5_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f238])).
% 0.22/0.50  fof(f378,plain,(
% 0.22/0.50    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | (~spl5_4 | ~spl5_15)),
% 0.22/0.50    inference(superposition,[],[f375,f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl5_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f173])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    ( ! [X1] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X1))) | ~r2_hidden(X1,sK0)) ) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f209,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    v3_ordinal1(sK0) | ~spl5_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f103])).
% 0.22/0.50  fof(f337,plain,(
% 0.22/0.50    ~spl5_30 | ~spl5_35 | ~spl5_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f329,f173,f335,f284])).
% 0.22/0.50  fof(f329,plain,(
% 0.22/0.50    ~r2_hidden(sK1,sK1) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_15),
% 0.22/0.50    inference(superposition,[],[f82,f174])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X4,X0] : (~r2_hidden(X4,k1_wellord1(X0,X4)) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X4,X2,X0] : (~r2_hidden(X4,X2) | k1_wellord1(X0,X4) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X1] : (X1 != X4 | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(rectify,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(flattening,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.22/0.50  fof(f326,plain,(
% 0.22/0.50    spl5_1 | ~spl5_4 | spl5_7 | ~spl5_3 | spl5_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f325,f170,f99,f134,f103,f91])).
% 0.22/0.50  fof(f325,plain,(
% 0.22/0.50    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | sK0 = sK1 | (~spl5_3 | spl5_14)),
% 0.22/0.50    inference(resolution,[],[f313,f113])).
% 0.22/0.50  fof(f313,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK1) | spl5_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f170])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    spl5_30),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f291])).
% 0.22/0.50  fof(f291,plain,(
% 0.22/0.50    $false | spl5_30),
% 0.22/0.50    inference(resolution,[],[f285,f54])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ~v1_relat_1(k1_wellord2(sK0)) | spl5_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f284])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    ~spl5_30 | spl5_31 | ~spl5_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f282,f238,f287,f284])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,sK1) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl5_24),
% 0.22/0.50    inference(forward_demodulation,[],[f281,f109])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl5_24),
% 0.22/0.50    inference(forward_demodulation,[],[f279,f109])).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl5_24),
% 0.22/0.50    inference(superposition,[],[f77,f239])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | r2_hidden(X0,k3_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1))) => (r2_hidden(X0,X1) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).
% 0.22/0.50  fof(f257,plain,(
% 0.22/0.50    ~spl5_4 | ~spl5_3 | spl5_19 | spl5_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f251,f217,f194,f99,f103])).
% 0.22/0.50  fof(f194,plain,(
% 0.22/0.50    spl5_19 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl5_22 <=> r1_ordinal1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl5_22),
% 0.22/0.50    inference(resolution,[],[f240,f74])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    ~r1_ordinal1(sK1,sK0) | spl5_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f241,plain,(
% 0.22/0.50    spl5_24 | ~spl5_22 | ~spl5_3 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f235,f103,f99,f217,f238])).
% 0.22/0.50  fof(f235,plain,(
% 0.22/0.50    ~r1_ordinal1(sK1,sK0) | k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | (~spl5_3 | ~spl5_4)),
% 0.22/0.50    inference(resolution,[],[f180,f100])).
% 0.22/0.50  fof(f180,plain,(
% 0.22/0.50    ( ! [X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X1,sK0) | k1_wellord2(X1) = k2_wellord1(k1_wellord2(sK0),X1)) ) | ~spl5_4),
% 0.22/0.50    inference(resolution,[],[f112,f104])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X0) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.50    inference(resolution,[],[f75,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    ~spl5_9 | spl5_23 | ~spl5_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f226,f191,f228,f144])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(X0,sK1) | ~r2_hidden(X0,sK0) | ~v1_relat_1(k1_wellord2(sK1))) ) | ~spl5_18),
% 0.22/0.50    inference(forward_demodulation,[],[f225,f109])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1))) ) | ~spl5_18),
% 0.22/0.50    inference(forward_demodulation,[],[f223,f109])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) | r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1))) ) | ~spl5_18),
% 0.22/0.50    inference(superposition,[],[f77,f192])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    spl5_18 | ~spl5_19 | ~spl5_3 | ~spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f182,f103,f99,f194,f191])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    ~r1_ordinal1(sK0,sK1) | k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | (~spl5_3 | ~spl5_4)),
% 0.22/0.50    inference(resolution,[],[f179,f104])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | ~r1_ordinal1(X0,sK1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(sK1),X0)) ) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f112,f100])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl5_9),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    $false | spl5_9),
% 0.22/0.50    inference(resolution,[],[f145,f54])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~v1_relat_1(k1_wellord2(sK1)) | spl5_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f144])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ~spl5_9 | ~spl5_11 | ~spl5_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f142,f138,f151,f144])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ~r2_hidden(sK0,sK0) | ~v1_relat_1(k1_wellord2(sK1)) | ~spl5_8),
% 0.22/0.50    inference(superposition,[],[f82,f139])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl5_7 | spl5_1 | spl5_8 | ~spl5_4 | ~spl5_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f132,f120,f103,f138,f91,f134])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    spl5_5 <=> ! [X0] : (r2_hidden(sK1,X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0 | sK1 = X0 | ~v3_ordinal1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | sK0 = sK1 | r2_hidden(sK1,sK0) | (~spl5_4 | ~spl5_5)),
% 0.22/0.50    inference(resolution,[],[f121,f104])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(sK1),X0) = X0 | sK1 = X0 | r2_hidden(sK1,X0)) ) | ~spl5_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f120])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ~spl5_3 | spl5_5 | ~spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f117,f99,f120,f99])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | sK1 = X0 | k1_wellord1(k1_wellord2(sK1),X0) = X0 | ~v3_ordinal1(sK1)) ) | ~spl5_3),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f115])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ( ! [X0] : (r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | sK1 = X0 | k1_wellord1(k1_wellord2(sK1),X0) = X0 | ~v3_ordinal1(sK1) | ~v3_ordinal1(X0)) ) | ~spl5_3),
% 0.22/0.50    inference(resolution,[],[f113,f64])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl5_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f50,f103])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    v3_ordinal1(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f37,f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl5_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f51,f99])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    v3_ordinal1(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl5_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f95])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~spl5_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f53,f91])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    sK0 != sK1),
% 0.22/0.50    inference(cnf_transformation,[],[f38])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (4513)------------------------------
% 0.22/0.50  % (4513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (4513)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (4513)Memory used [KB]: 10874
% 0.22/0.50  % (4513)Time elapsed: 0.067 s
% 0.22/0.50  % (4513)------------------------------
% 0.22/0.50  % (4513)------------------------------
% 0.22/0.50  % (4506)Success in time 0.137 s
%------------------------------------------------------------------------------
