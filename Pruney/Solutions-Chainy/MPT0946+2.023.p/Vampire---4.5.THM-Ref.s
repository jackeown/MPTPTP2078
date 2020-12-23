%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  189 ( 533 expanded)
%              Number of leaves         :   41 ( 189 expanded)
%              Depth                    :   19
%              Number of atoms          :  690 (2150 expanded)
%              Number of equality atoms :  114 ( 415 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f352,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f85,f89,f93,f117,f141,f193,f204,f206,f221,f226,f230,f235,f236,f255,f267,f277,f279,f283,f291,f304,f329,f332,f343,f346,f351])).

fof(f351,plain,
    ( spl4_1
    | spl4_9
    | ~ spl4_21
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f350,f233,f91,f87,f265,f188,f79])).

fof(f79,plain,
    ( spl4_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f188,plain,
    ( spl4_9
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f265,plain,
    ( spl4_21
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f87,plain,
    ( spl4_3
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f91,plain,
    ( spl4_4
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f233,plain,
    ( spl4_17
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f350,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = sK1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f185,f234])).

fof(f234,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f233])).

fof(f185,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = sK1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f182,f92])).

fof(f92,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ v3_ordinal1(X0)
        | ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),X0))
        | sK1 = k1_wellord1(k1_wellord2(X0),sK1)
        | sK1 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f181,f88])).

fof(f88,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | X0 = X1 ) ),
    inference(global_subsumption,[],[f56,f58,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | X0 = X1 ) ),
    inference(superposition,[],[f161,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = X1
      | X0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = X1
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f124,f56])).

fof(f124,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | k1_wellord1(k1_wellord2(X0),X1) = X1
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f58,f56])).

fof(f161,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(global_subsumption,[],[f50,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f159,f96])).

fof(f96,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f50,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f44])).

fof(f44,plain,(
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

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(X1)))
      | ~ r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0)))
      | ~ v1_relat_1(k1_wellord2(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f52,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f50,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f346,plain,
    ( ~ spl4_2
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f84,f344])).

fof(f344,plain,
    ( ! [X0] : ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))
    | ~ spl4_30 ),
    inference(resolution,[],[f342,f50])).

fof(f342,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k1_wellord2(X2))
        | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2)) )
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f341])).

fof(f341,plain,
    ( spl4_30
  <=> ! [X2] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f84,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_2
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f343,plain,
    ( ~ spl4_22
    | spl4_30
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f335,f302,f341,f271])).

fof(f271,plain,
    ( spl4_22
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f302,plain,
    ( spl4_25
  <=> ! [X0] :
        ( ~ r4_wellord1(X0,k1_wellord2(sK0))
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(k1_wellord2(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f335,plain,
    ( ! [X2] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl4_25 ),
    inference(duplicate_literal_removal,[],[f334])).

fof(f334,plain,
    ( ! [X2] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2))
        | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(X2))
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | ~ spl4_25 ),
    inference(resolution,[],[f318,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f318,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0))
        | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0)) )
    | ~ spl4_25 ),
    inference(resolution,[],[f303,f50])).

fof(f303,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r4_wellord1(X0,k1_wellord2(sK0))
        | ~ r4_wellord1(k1_wellord2(sK0),X0) )
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f302])).

fof(f332,plain,
    ( ~ spl4_2
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f84,f330])).

fof(f330,plain,
    ( ! [X0] : ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK1))
    | ~ spl4_28 ),
    inference(resolution,[],[f328,f50])).

fof(f328,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k1_wellord2(X2))
        | ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1)) )
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl4_28
  <=> ! [X2] :
        ( ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1))
        | ~ v1_relat_1(k1_wellord2(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f329,plain,
    ( ~ spl4_11
    | spl4_28
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f321,f202,f327,f199])).

fof(f199,plain,
    ( spl4_11
  <=> v1_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f202,plain,
    ( spl4_12
  <=> ! [X0] :
        ( ~ r4_wellord1(X0,k1_wellord2(sK1))
        | ~ v1_relat_1(X0)
        | ~ r4_wellord1(k1_wellord2(sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f321,plain,
    ( ! [X2] :
        ( ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1))
        | ~ v1_relat_1(k1_wellord2(sK1))
        | ~ v1_relat_1(k1_wellord2(X2)) )
    | ~ spl4_12 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X2] :
        ( ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1))
        | ~ r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1))
        | ~ v1_relat_1(k1_wellord2(sK1))
        | ~ v1_relat_1(k1_wellord2(X2)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f317,f53])).

fof(f317,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(X0))
        | ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(sK1)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f203,f50])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ r4_wellord1(X0,k1_wellord2(sK1))
        | ~ r4_wellord1(k1_wellord2(sK1),X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f202])).

fof(f304,plain,
    ( spl4_25
    | ~ spl4_22
    | spl4_16
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f300,f289,f228,f271,f302])).

fof(f228,plain,
    ( spl4_16
  <=> r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f289,plain,
    ( spl4_24
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f300,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK0))
        | ~ r4_wellord1(X0,k1_wellord2(sK0))
        | ~ r4_wellord1(k1_wellord2(sK0),X0)
        | ~ v1_relat_1(X0) )
    | spl4_16
    | ~ spl4_24 ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK0))
        | ~ r4_wellord1(X0,k1_wellord2(sK0))
        | ~ r4_wellord1(k1_wellord2(sK0),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | spl4_16
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f298,f290])).

fof(f290,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f289])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(X0,k1_wellord2(sK0))
        | ~ r4_wellord1(k1_wellord2(sK0),X0)
        | ~ v1_relat_1(k2_wellord1(k1_wellord2(sK0),sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | spl4_16
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f295,f290])).

fof(f295,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(X0,k2_wellord1(k1_wellord2(sK0),sK1))
        | ~ r4_wellord1(k1_wellord2(sK0),X0)
        | ~ v1_relat_1(k2_wellord1(k1_wellord2(sK0),sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_wellord2(sK0)) )
    | spl4_16 ),
    inference(resolution,[],[f229,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r4_wellord1(X0,X2)
      | ~ r4_wellord1(X1,X2)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_wellord1(X0,X2)
              | ~ r4_wellord1(X1,X2)
              | ~ r4_wellord1(X0,X1)
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
             => ( ( r4_wellord1(X1,X2)
                  & r4_wellord1(X0,X1) )
               => r4_wellord1(X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).

fof(f229,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | spl4_16 ),
    inference(avatar_component_clause,[],[f228])).

fof(f291,plain,
    ( spl4_24
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f285,f233,f289])).

fof(f285,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_17 ),
    inference(superposition,[],[f126,f234])).

fof(f126,plain,(
    ! [X0,X1] : k2_wellord1(k1_wellord2(X0),X1) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0) ),
    inference(superposition,[],[f125,f98])).

fof(f98,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0) ),
    inference(forward_demodulation,[],[f97,f96])).

fof(f97,plain,(
    ! [X0] : k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f51,f50])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f125,plain,(
    ! [X2,X0,X1] : k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1) ),
    inference(resolution,[],[f69,f50])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

fof(f283,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_13
    | spl4_1
    | spl4_15 ),
    inference(avatar_split_clause,[],[f281,f223,f79,f211,f91,f87])).

fof(f211,plain,
    ( spl4_13
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f223,plain,
    ( spl4_15
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f281,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | spl4_15 ),
    inference(resolution,[],[f254,f58])).

fof(f254,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f223])).

fof(f279,plain,(
    spl4_22 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl4_22 ),
    inference(resolution,[],[f272,f50])).

fof(f272,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f271])).

fof(f277,plain,
    ( ~ spl4_22
    | ~ spl4_11
    | ~ spl4_2
    | spl4_21 ),
    inference(avatar_split_clause,[],[f269,f265,f83,f199,f271])).

fof(f269,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_21 ),
    inference(resolution,[],[f266,f53])).

fof(f266,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f265])).

fof(f267,plain,
    ( ~ spl4_3
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f263,f233,f218,f265,f223,f87])).

fof(f218,plain,
    ( spl4_14
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f263,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_14
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f262,f234])).

fof(f262,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_14 ),
    inference(superposition,[],[f161,f219])).

fof(f219,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f218])).

fof(f255,plain,
    ( ~ spl4_3
    | ~ spl4_15
    | ~ spl4_10
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f253,f218,f139,f191,f223,f87])).

fof(f191,plain,
    ( spl4_10
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f139,plain,
    ( spl4_8
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f253,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_8
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f252,f140])).

fof(f140,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f252,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_14 ),
    inference(superposition,[],[f161,f219])).

fof(f236,plain,
    ( k1_wellord2(sK1) != k2_wellord1(k1_wellord2(sK0),sK1)
    | r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f235,plain,
    ( spl4_17
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f231,f106,f233])).

fof(f106,plain,
    ( spl4_5
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f231,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f107,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(resolution,[],[f66,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f107,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f230,plain,
    ( ~ spl4_4
    | ~ spl4_13
    | ~ spl4_16
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f207,f188,f228,f211,f91])).

fof(f207,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_9 ),
    inference(superposition,[],[f161,f189])).

fof(f189,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f188])).

fof(f226,plain,
    ( spl4_6
    | spl4_1
    | spl4_5
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f118,f91,f87,f106,f79,f110])).

fof(f110,plain,
    ( spl4_6
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f118,plain,
    ( r2_xboole_0(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f101,f88])).

fof(f101,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_xboole_0(sK0,X1)
        | sK0 = X1
        | r2_xboole_0(X1,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f57,f92])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | X0 = X1
      | r2_xboole_0(X0,X1)
      | ~ v3_ordinal1(X1)
      | r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f221,plain,
    ( spl4_14
    | ~ spl4_3
    | ~ spl4_4
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f215,f211,f79,f91,f87,f218])).

fof(f215,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | spl4_13 ),
    inference(resolution,[],[f212,f124])).

fof(f212,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f211])).

fof(f206,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | spl4_11 ),
    inference(resolution,[],[f200,f50])).

fof(f200,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f199])).

fof(f204,plain,
    ( ~ spl4_11
    | spl4_12
    | spl4_10 ),
    inference(avatar_split_clause,[],[f197,f191,f202,f199])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(X0,k1_wellord2(sK1))
        | ~ r4_wellord1(k1_wellord2(sK1),X0)
        | ~ v1_relat_1(k1_wellord2(sK1))
        | ~ v1_relat_1(X0) )
    | spl4_10 ),
    inference(duplicate_literal_removal,[],[f194])).

fof(f194,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(X0,k1_wellord2(sK1))
        | ~ r4_wellord1(k1_wellord2(sK1),X0)
        | ~ v1_relat_1(k1_wellord2(sK1))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k1_wellord2(sK1)) )
    | spl4_10 ),
    inference(resolution,[],[f192,f54])).

fof(f192,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( spl4_1
    | spl4_9
    | ~ spl4_10
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f186,f139,f91,f87,f191,f188,f79])).

fof(f186,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | sK0 = sK1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(forward_demodulation,[],[f185,f140])).

fof(f141,plain,
    ( spl4_8
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f137,f115,f139])).

fof(f115,plain,
    ( spl4_7
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f137,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f132,f116])).

fof(f116,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f132,plain,
    ( k2_wellord1(k1_wellord2(sK0),sK1) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_7 ),
    inference(superposition,[],[f127,f98])).

fof(f127,plain,
    ( ! [X2] : k2_wellord1(k2_wellord1(k1_wellord2(sK0),X2),sK1) = k2_wellord1(k1_wellord2(sK1),X2)
    | ~ spl4_7 ),
    inference(superposition,[],[f125,f116])).

fof(f117,plain,
    ( spl4_7
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f113,f110,f115])).

fof(f113,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_6 ),
    inference(resolution,[],[f111,f99])).

fof(f111,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f93,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f46,f91])).

fof(f46,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f89,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f47,f87])).

fof(f47,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f48,f83])).

fof(f48,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f81,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f49,f79])).

fof(f49,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (28498)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (28488)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (28494)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.48  % (28496)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.48  % (28500)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (28506)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (28506)Refutation not found, incomplete strategy% (28506)------------------------------
% 0.22/0.48  % (28506)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (28506)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (28506)Memory used [KB]: 10618
% 0.22/0.48  % (28506)Time elapsed: 0.072 s
% 0.22/0.48  % (28506)------------------------------
% 0.22/0.48  % (28506)------------------------------
% 0.22/0.49  % (28499)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.49  % (28495)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (28505)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.49  % (28487)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (28489)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (28490)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.49  % (28492)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (28486)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (28491)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (28487)Refutation not found, incomplete strategy% (28487)------------------------------
% 0.22/0.50  % (28487)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28501)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (28504)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (28497)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (28487)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28487)Memory used [KB]: 10618
% 0.22/0.50  % (28487)Time elapsed: 0.091 s
% 0.22/0.50  % (28487)------------------------------
% 0.22/0.50  % (28487)------------------------------
% 0.22/0.51  % (28493)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (28492)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f352,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f81,f85,f89,f93,f117,f141,f193,f204,f206,f221,f226,f230,f235,f236,f255,f267,f277,f279,f283,f291,f304,f329,f332,f343,f346,f351])).
% 0.22/0.51  fof(f351,plain,(
% 0.22/0.51    spl4_1 | spl4_9 | ~spl4_21 | ~spl4_3 | ~spl4_4 | ~spl4_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f350,f233,f91,f87,f265,f188,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    spl4_1 <=> sK0 = sK1),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.51  fof(f188,plain,(
% 0.22/0.51    spl4_9 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.51  fof(f265,plain,(
% 0.22/0.51    spl4_21 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    spl4_3 <=> v3_ordinal1(sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f91,plain,(
% 0.22/0.51    spl4_4 <=> v3_ordinal1(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.51  fof(f233,plain,(
% 0.22/0.51    spl4_17 <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.22/0.51  fof(f350,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK0 = sK1 | (~spl4_3 | ~spl4_4 | ~spl4_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f185,f234])).
% 0.22/0.51  fof(f234,plain,(
% 0.22/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f233])).
% 0.22/0.51  fof(f185,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK0 = sK1 | (~spl4_3 | ~spl4_4)),
% 0.22/0.51    inference(resolution,[],[f182,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    v3_ordinal1(sK0) | ~spl4_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f91])).
% 0.22/0.51  fof(f182,plain,(
% 0.22/0.51    ( ! [X0] : (~v3_ordinal1(X0) | ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),X0)) | sK1 = k1_wellord1(k1_wellord2(X0),sK1) | sK1 = X0) ) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f181,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    v3_ordinal1(sK1) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f87])).
% 0.22/0.51  fof(f181,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | X0 = X1) )),
% 0.22/0.51    inference(global_subsumption,[],[f56,f58,f180])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | X0 = X1) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f177])).
% 0.22/0.51  fof(f177,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | X0 = X1) )),
% 0.22/0.51    inference(superposition,[],[f161,f172])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = X1 | X0 = X1) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f171])).
% 0.22/0.51  fof(f171,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = X1 | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(resolution,[],[f124,f56])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = X1) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | k1_wellord1(k1_wellord2(X0),X1) = X1 | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(resolution,[],[f58,f56])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(global_subsumption,[],[f50,f160])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f159,f96])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.22/0.51    inference(global_subsumption,[],[f50,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(equality_resolution,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f43,f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(rectify,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(X1))) | ~r4_wellord1(k1_wellord2(X1),k2_wellord1(k1_wellord2(X1),k1_wellord1(k1_wellord2(X1),X0))) | ~v1_relat_1(k1_wellord2(X1)) | ~v3_ordinal1(X1)) )),
% 0.22/0.51    inference(resolution,[],[f52,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v2_wellord1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(flattening,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(flattening,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.51  fof(f346,plain,(
% 0.22/0.51    ~spl4_2 | ~spl4_30),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f345])).
% 0.22/0.51  fof(f345,plain,(
% 0.22/0.51    $false | (~spl4_2 | ~spl4_30)),
% 0.22/0.51    inference(subsumption_resolution,[],[f84,f344])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))) ) | ~spl4_30),
% 0.22/0.51    inference(resolution,[],[f342,f50])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    ( ! [X2] : (~v1_relat_1(k1_wellord2(X2)) | ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2))) ) | ~spl4_30),
% 0.22/0.51    inference(avatar_component_clause,[],[f341])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    spl4_30 <=> ! [X2] : (~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl4_2 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ~spl4_22 | spl4_30 | ~spl4_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f335,f302,f341,f271])).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    spl4_22 <=> v1_relat_1(k1_wellord2(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    spl4_25 <=> ! [X0] : (~r4_wellord1(X0,k1_wellord2(sK0)) | ~v1_relat_1(X0) | ~r4_wellord1(k1_wellord2(sK0),X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    ( ! [X2] : (~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl4_25),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f334])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    ( ! [X2] : (~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2)) | ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(X2)) | ~v1_relat_1(k1_wellord2(sK0))) ) | ~spl4_25),
% 0.22/0.51    inference(resolution,[],[f318,f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.51  fof(f318,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(sK0)) | ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(X0))) ) | ~spl4_25),
% 0.22/0.51    inference(resolution,[],[f303,f50])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(sK0)) | ~r4_wellord1(k1_wellord2(sK0),X0)) ) | ~spl4_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f302])).
% 0.22/0.51  fof(f332,plain,(
% 0.22/0.51    ~spl4_2 | ~spl4_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f331])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    $false | (~spl4_2 | ~spl4_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f84,f330])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(sK1))) ) | ~spl4_28),
% 0.22/0.51    inference(resolution,[],[f328,f50])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    ( ! [X2] : (~v1_relat_1(k1_wellord2(X2)) | ~r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1))) ) | ~spl4_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f327])).
% 0.22/0.51  fof(f327,plain,(
% 0.22/0.51    spl4_28 <=> ! [X2] : (~r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(X2)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    ~spl4_11 | spl4_28 | ~spl4_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f321,f202,f327,f199])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    spl4_11 <=> v1_relat_1(k1_wellord2(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    spl4_12 <=> ! [X0] : (~r4_wellord1(X0,k1_wellord2(sK1)) | ~v1_relat_1(X0) | ~r4_wellord1(k1_wellord2(sK1),X0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    ( ! [X2] : (~r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(X2))) ) | ~spl4_12),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f320])).
% 0.22/0.51  fof(f320,plain,(
% 0.22/0.51    ( ! [X2] : (~r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1)) | ~r4_wellord1(k1_wellord2(X2),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(X2))) ) | ~spl4_12),
% 0.22/0.51    inference(resolution,[],[f317,f53])).
% 0.22/0.51  fof(f317,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK1),k1_wellord2(X0)) | ~r4_wellord1(k1_wellord2(X0),k1_wellord2(sK1))) ) | ~spl4_12),
% 0.22/0.51    inference(resolution,[],[f203,f50])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | ~r4_wellord1(X0,k1_wellord2(sK1)) | ~r4_wellord1(k1_wellord2(sK1),X0)) ) | ~spl4_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f202])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    spl4_25 | ~spl4_22 | spl4_16 | ~spl4_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f300,f289,f228,f271,f302])).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    spl4_16 <=> r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    spl4_24 <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(k1_wellord2(sK0)) | ~r4_wellord1(X0,k1_wellord2(sK0)) | ~r4_wellord1(k1_wellord2(sK0),X0) | ~v1_relat_1(X0)) ) | (spl4_16 | ~spl4_24)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f299])).
% 0.22/0.51  fof(f299,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(k1_wellord2(sK0)) | ~r4_wellord1(X0,k1_wellord2(sK0)) | ~r4_wellord1(k1_wellord2(sK0),X0) | ~v1_relat_1(X0) | ~v1_relat_1(k1_wellord2(sK0))) ) | (spl4_16 | ~spl4_24)),
% 0.22/0.51    inference(forward_demodulation,[],[f298,f290])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f289])).
% 0.22/0.51  fof(f298,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(X0,k1_wellord2(sK0)) | ~r4_wellord1(k1_wellord2(sK0),X0) | ~v1_relat_1(k2_wellord1(k1_wellord2(sK0),sK1)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_wellord2(sK0))) ) | (spl4_16 | ~spl4_24)),
% 0.22/0.51    inference(forward_demodulation,[],[f295,f290])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(X0,k2_wellord1(k1_wellord2(sK0),sK1)) | ~r4_wellord1(k1_wellord2(sK0),X0) | ~v1_relat_1(k2_wellord1(k1_wellord2(sK0),sK1)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_wellord2(sK0))) ) | spl4_16),
% 0.22/0.51    inference(resolution,[],[f229,f54])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (r4_wellord1(X0,X2) | ~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r4_wellord1(X0,X2) | (~r4_wellord1(X1,X2) | ~r4_wellord1(X0,X1))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => ((r4_wellord1(X1,X2) & r4_wellord1(X0,X1)) => r4_wellord1(X0,X2)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_wellord1)).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | spl4_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f228])).
% 0.22/0.51  fof(f291,plain,(
% 0.22/0.51    spl4_24 | ~spl4_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f285,f233,f289])).
% 0.22/0.51  fof(f285,plain,(
% 0.22/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_17),
% 0.22/0.51    inference(superposition,[],[f126,f234])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_wellord1(k1_wellord2(X0),X1) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X0)) )),
% 0.22/0.51    inference(superposition,[],[f125,f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f97,f96])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X0] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X0),k3_relat_1(k1_wellord2(X0)))) )),
% 0.22/0.51    inference(resolution,[],[f51,f50])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_relat_1(X0) | k2_wellord1(X0,k3_relat_1(X0)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (k2_wellord1(X0,k3_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (v1_relat_1(X0) => k2_wellord1(X0,k3_relat_1(X0)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k2_wellord1(k2_wellord1(k1_wellord2(X0),X1),X2) = k2_wellord1(k2_wellord1(k1_wellord2(X0),X2),X1)) )),
% 0.22/0.51    inference(resolution,[],[f69,f50])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0) | ~v1_relat_1(X2))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => k2_wellord1(k2_wellord1(X2,X0),X1) = k2_wellord1(k2_wellord1(X2,X1),X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).
% 0.22/0.51  fof(f283,plain,(
% 0.22/0.51    ~spl4_3 | ~spl4_4 | spl4_13 | spl4_1 | spl4_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f281,f223,f79,f211,f91,f87])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl4_13 <=> r2_hidden(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    spl4_15 <=> r2_hidden(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.51  fof(f281,plain,(
% 0.22/0.51    sK0 = sK1 | r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | spl4_15),
% 0.22/0.51    inference(resolution,[],[f254,f58])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    ~r2_hidden(sK0,sK1) | spl4_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f223])).
% 0.22/0.51  fof(f279,plain,(
% 0.22/0.51    spl4_22),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f278])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    $false | spl4_22),
% 0.22/0.51    inference(resolution,[],[f272,f50])).
% 0.22/0.51  fof(f272,plain,(
% 0.22/0.51    ~v1_relat_1(k1_wellord2(sK0)) | spl4_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f271])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ~spl4_22 | ~spl4_11 | ~spl4_2 | spl4_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f269,f265,f83,f199,f271])).
% 0.22/0.51  fof(f269,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | spl4_21),
% 0.22/0.51    inference(resolution,[],[f266,f53])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | spl4_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f265])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    ~spl4_3 | ~spl4_15 | ~spl4_21 | ~spl4_14 | ~spl4_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f263,f233,f218,f265,f223,f87])).
% 0.22/0.51  fof(f218,plain,(
% 0.22/0.51    spl4_14 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | (~spl4_14 | ~spl4_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f262,f234])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~spl4_14),
% 0.22/0.51    inference(superposition,[],[f161,f219])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl4_14),
% 0.22/0.51    inference(avatar_component_clause,[],[f218])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    ~spl4_3 | ~spl4_15 | ~spl4_10 | ~spl4_8 | ~spl4_14),
% 0.22/0.51    inference(avatar_split_clause,[],[f253,f218,f139,f191,f223,f87])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    spl4_10 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    spl4_8 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | (~spl4_8 | ~spl4_14)),
% 0.22/0.51    inference(forward_demodulation,[],[f252,f140])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f139])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~spl4_14),
% 0.22/0.51    inference(superposition,[],[f161,f219])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    k1_wellord2(sK1) != k2_wellord1(k1_wellord2(sK0),sK1) | r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    spl4_17 | ~spl4_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f231,f106,f233])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    spl4_5 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_5),
% 0.22/0.51    inference(resolution,[],[f107,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.51    inference(resolution,[],[f66,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    r2_xboole_0(sK0,sK1) | ~spl4_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f106])).
% 0.22/0.51  fof(f230,plain,(
% 0.22/0.51    ~spl4_4 | ~spl4_13 | ~spl4_16 | ~spl4_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f207,f188,f228,f211,f91])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~spl4_9),
% 0.22/0.51    inference(superposition,[],[f161,f189])).
% 0.22/0.51  fof(f189,plain,(
% 0.22/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl4_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f188])).
% 0.22/0.51  fof(f226,plain,(
% 0.22/0.51    spl4_6 | spl4_1 | spl4_5 | ~spl4_3 | ~spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f118,f91,f87,f106,f79,f110])).
% 0.22/0.51  fof(f110,plain,(
% 0.22/0.51    spl4_6 <=> r2_xboole_0(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    r2_xboole_0(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0) | (~spl4_3 | ~spl4_4)),
% 0.22/0.51    inference(resolution,[],[f101,f88])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    ( ! [X1] : (~v3_ordinal1(X1) | r2_xboole_0(sK0,X1) | sK0 = X1 | r2_xboole_0(X1,sK0)) ) | ~spl4_4),
% 0.22/0.51    inference(resolution,[],[f57,f92])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1) | r2_xboole_0(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(flattening,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl4_14 | ~spl4_3 | ~spl4_4 | spl4_1 | spl4_13),
% 0.22/0.51    inference(avatar_split_clause,[],[f215,f211,f79,f91,f87,f218])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    sK0 = sK1 | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | spl4_13),
% 0.22/0.51    inference(resolution,[],[f212,f124])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ~r2_hidden(sK1,sK0) | spl4_13),
% 0.22/0.51    inference(avatar_component_clause,[],[f211])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    spl4_11),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    $false | spl4_11),
% 0.22/0.51    inference(resolution,[],[f200,f50])).
% 0.22/0.51  fof(f200,plain,(
% 0.22/0.51    ~v1_relat_1(k1_wellord2(sK1)) | spl4_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f199])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ~spl4_11 | spl4_12 | spl4_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f197,f191,f202,f199])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(X0,k1_wellord2(sK1)) | ~r4_wellord1(k1_wellord2(sK1),X0) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(X0)) ) | spl4_10),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    ( ! [X0] : (~r4_wellord1(X0,k1_wellord2(sK1)) | ~r4_wellord1(k1_wellord2(sK1),X0) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(X0) | ~v1_relat_1(k1_wellord2(sK1))) ) | spl4_10),
% 0.22/0.51    inference(resolution,[],[f192,f54])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) | spl4_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f191])).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    spl4_1 | spl4_9 | ~spl4_10 | ~spl4_3 | ~spl4_4 | ~spl4_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f186,f139,f91,f87,f191,f188,f79])).
% 0.22/0.51  fof(f186,plain,(
% 0.22/0.51    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK1)) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | sK0 = sK1 | (~spl4_3 | ~spl4_4 | ~spl4_8)),
% 0.22/0.51    inference(forward_demodulation,[],[f185,f140])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    spl4_8 | ~spl4_7),
% 0.22/0.51    inference(avatar_split_clause,[],[f137,f115,f139])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl4_7 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_7),
% 0.22/0.51    inference(forward_demodulation,[],[f132,f116])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f115])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    k2_wellord1(k1_wellord2(sK0),sK1) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_7),
% 0.22/0.51    inference(superposition,[],[f127,f98])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X2] : (k2_wellord1(k2_wellord1(k1_wellord2(sK0),X2),sK1) = k2_wellord1(k1_wellord2(sK1),X2)) ) | ~spl4_7),
% 0.22/0.51    inference(superposition,[],[f125,f116])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl4_7 | ~spl4_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f113,f110,f115])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_6),
% 0.22/0.51    inference(resolution,[],[f111,f99])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    r2_xboole_0(sK1,sK0) | ~spl4_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f110])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    spl4_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f46,f91])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    v3_ordinal1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f18,f39,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f14])).
% 0.22/0.51  fof(f14,conjecture,(
% 0.22/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f47,f87])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    v3_ordinal1(sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f48,f83])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ~spl4_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f49,f79])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(cnf_transformation,[],[f40])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (28492)------------------------------
% 0.22/0.51  % (28492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28492)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (28492)Memory used [KB]: 10874
% 0.22/0.51  % (28492)Time elapsed: 0.052 s
% 0.22/0.51  % (28492)------------------------------
% 0.22/0.51  % (28492)------------------------------
% 0.22/0.51  % (28484)Success in time 0.151 s
%------------------------------------------------------------------------------
