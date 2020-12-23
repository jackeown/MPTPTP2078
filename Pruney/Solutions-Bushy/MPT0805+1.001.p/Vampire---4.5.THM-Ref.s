%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0805+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:41 EST 2020

% Result     : Theorem 3.34s
% Output     : Refutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  247 ( 516 expanded)
%              Number of leaves         :   62 ( 226 expanded)
%              Depth                    :   11
%              Number of atoms          :  966 (2010 expanded)
%              Number of equality atoms :  141 ( 357 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f115,f119,f123,f127,f131,f135,f146,f237,f249,f257,f263,f301,f403,f438,f482,f495,f497,f502,f522,f550,f590,f600,f1038,f1378,f1379,f1420,f1539,f1547,f1633,f2371,f2380,f3078,f3087,f3203,f3242,f3245,f3273,f3446])).

fof(f3446,plain,
    ( spl6_178
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_121
    | ~ spl6_325 ),
    inference(avatar_split_clause,[],[f3375,f3240,f1036,f129,f133,f1631])).

fof(f1631,plain,
    ( spl6_178
  <=> ! [X79,X80] :
        ( k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X79)),o_0_0_xboole_0)
        | ~ r2_hidden(X80,k1_wellord1(sK2,X79)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_178])])).

fof(f133,plain,
    ( spl6_7
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f129,plain,
    ( spl6_6
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f1036,plain,
    ( spl6_121
  <=> ! [X1,X0] :
        ( r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | m1_subset_1(k1_wellord1(sK2,X1),k1_zfmisc_1(k1_wellord1(sK2,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f3240,plain,
    ( spl6_325
  <=> o_0_0_xboole_0 = k1_wellord1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_325])])).

fof(f3375,plain,
    ( ! [X88,X89] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X88)),o_0_0_xboole_0)
        | ~ r2_hidden(X89,k1_wellord1(sK2,X88)) )
    | ~ spl6_6
    | ~ spl6_121
    | ~ spl6_325 ),
    inference(superposition,[],[f1142,f3241])).

fof(f3241,plain,
    ( o_0_0_xboole_0 = k1_wellord1(sK2,sK0)
    | ~ spl6_325 ),
    inference(avatar_component_clause,[],[f3240])).

fof(f1142,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_xboole_0(k1_wellord1(sK2,X3))
        | k2_wellord1(sK2,k1_wellord1(sK2,X3)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X4)),k1_wellord1(sK2,X3))
        | ~ r2_hidden(X5,k1_wellord1(sK2,X4)) )
    | ~ spl6_6
    | ~ spl6_121 ),
    inference(resolution,[],[f1139,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f1139,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_wellord1(sK2,X0),k1_zfmisc_1(k1_wellord1(sK2,X1)))
        | k2_wellord1(sK2,k1_wellord1(sK2,X1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X1)) )
    | ~ spl6_6
    | ~ spl6_121 ),
    inference(resolution,[],[f1099,f130])).

fof(f130,plain,
    ( v1_relat_1(sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f129])).

fof(f1099,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k2_wellord1(k2_wellord1(X2,k1_wellord1(sK2,X0)),k1_wellord1(sK2,X1)) = k2_wellord1(X2,k1_wellord1(sK2,X1))
        | m1_subset_1(k1_wellord1(sK2,X0),k1_zfmisc_1(k1_wellord1(sK2,X1))) )
    | ~ spl6_121 ),
    inference(resolution,[],[f1037,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(k2_wellord1(X2,X1),X0) = k2_wellord1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f1037,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | m1_subset_1(k1_wellord1(sK2,X1),k1_zfmisc_1(k1_wellord1(sK2,X0))) )
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f3273,plain,
    ( spl6_266
    | spl6_2
    | spl6_37
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_178 ),
    inference(avatar_split_clause,[],[f3041,f1631,f261,f121,f117,f401,f113,f2365])).

fof(f2365,plain,
    ( spl6_266
  <=> k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_266])])).

fof(f113,plain,
    ( spl6_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f401,plain,
    ( spl6_37
  <=> r2_hidden(sK1,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f117,plain,
    ( spl6_3
  <=> r2_hidden(sK1,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f121,plain,
    ( spl6_4
  <=> r2_hidden(sK0,k3_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f261,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f3041,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | sK0 = sK1
    | k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),o_0_0_xboole_0)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_178 ),
    inference(resolution,[],[f2542,f118])).

fof(f118,plain,
    ( r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f2542,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X0,k1_wellord1(sK2,sK0))
        | sK0 = X0
        | k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X0)),o_0_0_xboole_0) )
    | ~ spl6_4
    | ~ spl6_17
    | ~ spl6_178 ),
    inference(resolution,[],[f265,f1632])).

fof(f1632,plain,
    ( ! [X80,X79] :
        ( ~ r2_hidden(X80,k1_wellord1(sK2,X79))
        | k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X79)),o_0_0_xboole_0) )
    | ~ spl6_178 ),
    inference(avatar_component_clause,[],[f1631])).

fof(f265,plain,
    ( ! [X1] :
        ( r2_hidden(sK0,k1_wellord1(sK2,X1))
        | r2_hidden(X1,k1_wellord1(sK2,sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK0 = X1 )
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(resolution,[],[f262,f122])).

fof(f122,plain,
    ( r2_hidden(sK0,k3_relat_1(sK2))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f262,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | r2_hidden(X0,k1_wellord1(sK2,X1))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f261])).

fof(f3245,plain,
    ( o_0_0_xboole_0 != k1_wellord1(sK2,sK0)
    | k1_wellord1(sK2,sK0) != k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | k2_wellord1(sK2,o_0_0_xboole_0) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),o_0_0_xboole_0)
    | k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3242,plain,
    ( spl6_325
    | ~ spl6_7
    | ~ spl6_108 ),
    inference(avatar_split_clause,[],[f3224,f948,f133,f3240])).

fof(f948,plain,
    ( spl6_108
  <=> v1_xboole_0(k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_108])])).

fof(f3224,plain,
    ( o_0_0_xboole_0 = k1_wellord1(sK2,sK0)
    | ~ spl6_7
    | ~ spl6_108 ),
    inference(resolution,[],[f983,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl6_7 ),
    inference(resolution,[],[f98,f134])).

fof(f134,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f983,plain,
    ( v1_xboole_0(k1_wellord1(sK2,sK0))
    | ~ spl6_108 ),
    inference(avatar_component_clause,[],[f948])).

fof(f3203,plain,
    ( spl6_2
    | ~ spl6_4
    | spl6_49
    | ~ spl6_3
    | ~ spl6_17
    | spl6_37 ),
    inference(avatar_split_clause,[],[f817,f401,f261,f117,f460,f121,f113])).

fof(f460,plain,
    ( spl6_49
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f817,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | sK0 = sK1
    | ~ spl6_3
    | ~ spl6_17
    | spl6_37 ),
    inference(resolution,[],[f264,f402])).

fof(f402,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f401])).

fof(f264,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_wellord1(sK2,X0))
        | r2_hidden(X0,k1_wellord1(sK2,sK1))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | sK1 = X0 )
    | ~ spl6_3
    | ~ spl6_17 ),
    inference(resolution,[],[f262,f118])).

fof(f3087,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK1)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f3078,plain,
    ( ~ spl6_6
    | spl6_308
    | spl6_117
    | ~ spl6_6
    | ~ spl6_37
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f3059,f1036,f401,f129,f1020,f3065,f129])).

fof(f3065,plain,
    ( spl6_308
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_308])])).

fof(f1020,plain,
    ( spl6_117
  <=> v1_xboole_0(k1_wellord1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_117])])).

fof(f3059,plain,
    ( v1_xboole_0(k1_wellord1(sK2,sK1))
    | k2_wellord1(sK2,k1_wellord1(sK2,sK1)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl6_6
    | ~ spl6_37
    | ~ spl6_121 ),
    inference(resolution,[],[f1431,f107])).

fof(f107,plain,(
    ! [X4,X0] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X4))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0] :
      ( ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X4) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                | sK5(X0,X1,X2) = X1
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
                  & sK5(X0,X1,X2) != X1 )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
          | sK5(X0,X1,X2) = X1
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK5(X0,X1,X2),X1),X0)
            & sK5(X0,X1,X2) != X1 )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
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
    inference(rectify,[],[f59])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f1431,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_wellord1(sK2,X0))
        | v1_xboole_0(k1_wellord1(sK2,X0))
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,X0)) )
    | ~ spl6_6
    | ~ spl6_37
    | ~ spl6_121 ),
    inference(resolution,[],[f570,f1156])).

fof(f1156,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k1_wellord1(sK2,X1))
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0))
        | v1_xboole_0(k1_wellord1(sK2,X0))
        | r2_hidden(X2,k1_wellord1(sK2,X0)) )
    | ~ spl6_6
    | ~ spl6_121 ),
    inference(resolution,[],[f1141,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1141,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_wellord1(sK2,X0))
        | k2_wellord1(sK2,k1_wellord1(sK2,X0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),k1_wellord1(sK2,X0))
        | ~ r2_hidden(X2,k1_wellord1(sK2,X1)) )
    | ~ spl6_6
    | ~ spl6_121 ),
    inference(resolution,[],[f1139,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f570,plain,
    ( r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f401])).

fof(f2380,plain,
    ( ~ spl6_155
    | spl6_157
    | ~ spl6_267 ),
    inference(avatar_split_clause,[],[f2378,f2369,f1545,f1537])).

fof(f1537,plain,
    ( spl6_155
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_155])])).

fof(f1545,plain,
    ( spl6_157
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_157])])).

fof(f2369,plain,
    ( spl6_267
  <=> k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_267])])).

fof(f2378,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0))
    | spl6_157
    | ~ spl6_267 ),
    inference(forward_demodulation,[],[f1546,f2370])).

fof(f2370,plain,
    ( k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),o_0_0_xboole_0)
    | ~ spl6_267 ),
    inference(avatar_component_clause,[],[f2369])).

fof(f1546,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),o_0_0_xboole_0))
    | spl6_157 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f2371,plain,
    ( spl6_267
    | ~ spl6_37
    | ~ spl6_178 ),
    inference(avatar_split_clause,[],[f2359,f1631,f401,f2369])).

fof(f2359,plain,
    ( k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),o_0_0_xboole_0)
    | ~ spl6_37
    | ~ spl6_178 ),
    inference(resolution,[],[f1632,f570])).

fof(f1633,plain,
    ( spl6_178
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_121
    | ~ spl6_150 ),
    inference(avatar_split_clause,[],[f1515,f1418,f1036,f129,f133,f1631])).

fof(f1418,plain,
    ( spl6_150
  <=> o_0_0_xboole_0 = k1_wellord1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).

fof(f1515,plain,
    ( ! [X80,X79] :
        ( ~ v1_xboole_0(o_0_0_xboole_0)
        | k2_wellord1(sK2,o_0_0_xboole_0) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X79)),o_0_0_xboole_0)
        | ~ r2_hidden(X80,k1_wellord1(sK2,X79)) )
    | ~ spl6_6
    | ~ spl6_121
    | ~ spl6_150 ),
    inference(superposition,[],[f1142,f1419])).

fof(f1419,plain,
    ( o_0_0_xboole_0 = k1_wellord1(sK2,sK1)
    | ~ spl6_150 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1547,plain,
    ( ~ spl6_157
    | spl6_36
    | ~ spl6_150 ),
    inference(avatar_split_clause,[],[f1445,f1418,f398,f1545])).

fof(f398,plain,
    ( spl6_36
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f1445,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),o_0_0_xboole_0))
    | spl6_36
    | ~ spl6_150 ),
    inference(superposition,[],[f399,f1419])).

fof(f399,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f398])).

fof(f1539,plain,
    ( spl6_155
    | ~ spl6_1
    | ~ spl6_150 ),
    inference(avatar_split_clause,[],[f1442,f1418,f109,f1537])).

fof(f109,plain,
    ( spl6_1
  <=> r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1442,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,o_0_0_xboole_0))
    | ~ spl6_1
    | ~ spl6_150 ),
    inference(superposition,[],[f110,f1419])).

fof(f110,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1420,plain,
    ( spl6_150
    | ~ spl6_7
    | ~ spl6_117 ),
    inference(avatar_split_clause,[],[f1408,f1020,f133,f1418])).

fof(f1408,plain,
    ( o_0_0_xboole_0 = k1_wellord1(sK2,sK1)
    | ~ spl6_7
    | ~ spl6_117 ),
    inference(resolution,[],[f1077,f137])).

fof(f1077,plain,
    ( v1_xboole_0(k1_wellord1(sK2,sK1))
    | ~ spl6_117 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f1379,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) != k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1378,plain,
    ( spl6_54
    | spl6_143
    | ~ spl6_6
    | ~ spl6_49
    | spl6_108
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f1374,f1036,f948,f460,f129,f1331,f480])).

fof(f480,plain,
    ( spl6_54
  <=> r2_hidden(sK0,k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f1331,plain,
    ( spl6_143
  <=> k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_143])])).

fof(f1374,plain,
    ( k2_wellord1(sK2,k1_wellord1(sK2,sK0)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))
    | r2_hidden(sK0,k1_wellord1(sK2,sK0))
    | ~ spl6_6
    | ~ spl6_49
    | spl6_108
    | ~ spl6_121 ),
    inference(resolution,[],[f1366,f949])).

fof(f949,plain,
    ( ~ v1_xboole_0(k1_wellord1(sK2,sK0))
    | spl6_108 ),
    inference(avatar_component_clause,[],[f948])).

fof(f1366,plain,
    ( ! [X7] :
        ( v1_xboole_0(k1_wellord1(sK2,X7))
        | k2_wellord1(sK2,k1_wellord1(sK2,X7)) = k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,X7))
        | r2_hidden(sK0,k1_wellord1(sK2,X7)) )
    | ~ spl6_6
    | ~ spl6_49
    | ~ spl6_121 ),
    inference(resolution,[],[f1156,f524])).

fof(f524,plain,
    ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f460])).

fof(f1038,plain,
    ( spl6_121
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f1033,f129,f125,f1036])).

fof(f125,plain,
    ( spl6_5
  <=> v2_wellord1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f1033,plain,
    ( ! [X0,X1] :
        ( ~ v2_wellord1(sK2)
        | r1_tarski(k1_wellord1(sK2,X0),k1_wellord1(sK2,X1))
        | m1_subset_1(k1_wellord1(sK2,X1),k1_zfmisc_1(k1_wellord1(sK2,X0))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f152,f130])).

fof(f152,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | ~ v2_wellord1(X4)
      | r1_tarski(k1_wellord1(X4,X5),k1_wellord1(X4,X6))
      | m1_subset_1(k1_wellord1(X4,X6),k1_zfmisc_1(k1_wellord1(X4,X5))) ) ),
    inference(resolution,[],[f139,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X0,X1),k1_wellord1(X0,X2))
      | ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | r1_tarski(k1_wellord1(X0,X2),k1_wellord1(X0,X1)) ) ),
    inference(resolution,[],[f99,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r3_xboole_0(X0,X1)
      | r1_tarski(X0,X1)
      | r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | r1_tarski(X0,X1)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
     => ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( v2_wellord1(X2)
       => r3_xboole_0(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord1)).

fof(f600,plain,
    ( ~ spl6_46
    | spl6_57 ),
    inference(avatar_split_clause,[],[f599,f493,f451])).

fof(f451,plain,
    ( spl6_46
  <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f493,plain,
    ( spl6_57
  <=> v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f599,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | spl6_57 ),
    inference(resolution,[],[f494,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f494,plain,
    ( ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | spl6_57 ),
    inference(avatar_component_clause,[],[f493])).

fof(f590,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_32
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f584,f401,f374,f125,f129])).

fof(f374,plain,
    ( spl6_32
  <=> k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f584,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_37 ),
    inference(resolution,[],[f570,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0)
      | ~ r2_hidden(X0,k1_wellord1(X2,X1))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X0,k1_wellord1(X2,X1))
          & v2_wellord1(X2) )
       => k1_wellord1(X2,X0) = k1_wellord1(k2_wellord1(X2,k1_wellord1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_wellord1)).

fof(f550,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_47 ),
    inference(avatar_split_clause,[],[f548,f454,f125,f129])).

fof(f454,plain,
    ( spl6_47
  <=> v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f548,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_47 ),
    inference(resolution,[],[f455,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( v2_wellord1(k2_wellord1(X1,X0))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_wellord1)).

fof(f455,plain,
    ( ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | spl6_47 ),
    inference(avatar_component_clause,[],[f454])).

fof(f522,plain,
    ( ~ spl6_3
    | spl6_2
    | spl6_33
    | ~ spl6_22
    | spl6_37 ),
    inference(avatar_split_clause,[],[f519,f401,f299,f377,f113,f117])).

fof(f377,plain,
    ( spl6_33
  <=> k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f299,plain,
    ( spl6_22
  <=> ! [X1] :
        ( r2_hidden(X1,k1_wellord1(sK2,sK0))
        | k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK0)
        | sK0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f519,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | sK0 = sK1
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ spl6_22
    | spl6_37 ),
    inference(resolution,[],[f402,f300])).

fof(f300,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_wellord1(sK2,sK0))
        | k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK0)
        | sK0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f299])).

fof(f502,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_35 ),
    inference(avatar_split_clause,[],[f500,f395,f125,f129])).

fof(f395,plain,
    ( spl6_35
  <=> v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f500,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_35 ),
    inference(resolution,[],[f396,f92])).

fof(f396,plain,
    ( ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_35 ),
    inference(avatar_component_clause,[],[f395])).

fof(f497,plain,
    ( ~ spl6_6
    | spl6_46 ),
    inference(avatar_split_clause,[],[f496,f451,f129])).

fof(f496,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_46 ),
    inference(resolution,[],[f452,f91])).

fof(f452,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | spl6_46 ),
    inference(avatar_component_clause,[],[f451])).

fof(f495,plain,
    ( ~ spl6_56
    | ~ spl6_46
    | ~ spl6_47
    | ~ spl6_57
    | ~ spl6_49
    | ~ spl6_8
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f488,f377,f143,f460,f493,f454,f451,f490])).

fof(f490,plain,
    ( spl6_56
  <=> r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f143,plain,
    ( spl6_8
  <=> ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f488,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
    | ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl6_8
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f447,f144])).

fof(f144,plain,
    ( ! [X0] : k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f447,plain,
    ( ~ v1_relat_1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r4_wellord1(k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK0,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1))))
    | ~ spl6_33 ),
    inference(superposition,[],[f150,f378])).

fof(f378,plain,
    ( k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)),sK0)
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f377])).

fof(f150,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X0)),X1)
      | ~ r2_hidden(X0,k3_relat_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(k2_wellord1(X1,k1_wellord1(X1,X0)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(resolution,[],[f71,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f482,plain,
    ( ~ spl6_46
    | ~ spl6_54
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f444,f377,f480,f451])).

fof(f444,plain,
    ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK0))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    | ~ spl6_33 ),
    inference(superposition,[],[f107,f378])).

fof(f438,plain,
    ( ~ spl6_6
    | spl6_34 ),
    inference(avatar_split_clause,[],[f437,f392,f129])).

fof(f392,plain,
    ( spl6_34
  <=> v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f437,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_34 ),
    inference(resolution,[],[f393,f91])).

fof(f393,plain,
    ( ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f392])).

fof(f403,plain,
    ( ~ spl6_34
    | ~ spl6_35
    | ~ spl6_36
    | ~ spl6_37
    | ~ spl6_8
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f390,f374,f143,f401,f398,f395,f392])).

fof(f390,plain,
    ( ~ r2_hidden(sK1,k1_wellord1(sK2,sK0))
    | ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl6_8
    | ~ spl6_32 ),
    inference(forward_demodulation,[],[f380,f144])).

fof(f380,plain,
    ( ~ r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k1_wellord1(sK2,sK1)))
    | ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0))))
    | ~ v2_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ v1_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)))
    | ~ spl6_32 ),
    inference(superposition,[],[f71,f375])).

fof(f375,plain,
    ( k1_wellord1(sK2,sK1) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),sK1)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f374])).

fof(f301,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_22
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f295,f261,f121,f299,f125,f129])).

fof(f295,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_wellord1(sK2,sK0))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | sK0 = X1
        | k1_wellord1(sK2,sK0) = k1_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,X1)),sK0)
        | ~ v2_wellord1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_4
    | ~ spl6_17 ),
    inference(resolution,[],[f265,f101])).

fof(f263,plain,
    ( ~ spl6_6
    | spl6_17
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f259,f255,f261,f129])).

fof(f255,plain,
    ( spl6_16
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f259,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_16 ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k1_wellord1(sK2,X1))
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl6_16 ),
    inference(resolution,[],[f256,f104])).

fof(f104,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X1),X0)
      | r2_hidden(X4,k1_wellord1(X0,X1))
      | X1 = X4
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2)) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f255])).

fof(f257,plain,
    ( ~ spl6_6
    | spl6_16
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f253,f235,f255,f129])).

fof(f235,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | ~ v1_relat_1(sK2) )
    | ~ spl6_13 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | X0 = X1
        | r2_hidden(X1,k1_wellord1(sK2,X0))
        | X0 = X1
        | ~ v1_relat_1(sK2) )
    | ~ spl6_13 ),
    inference(resolution,[],[f236,f104])).

fof(f236,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2)
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | X0 = X1 )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f235])).

fof(f249,plain,
    ( ~ spl6_6
    | ~ spl6_5
    | spl6_12 ),
    inference(avatar_split_clause,[],[f240,f232,f125,f129])).

fof(f232,plain,
    ( spl6_12
  <=> v6_relat_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f240,plain,
    ( ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_12 ),
    inference(resolution,[],[f233,f81])).

fof(f81,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_wellord1)).

fof(f233,plain,
    ( ~ v6_relat_2(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f232])).

fof(f237,plain,
    ( ~ spl6_12
    | spl6_13
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f229,f129,f235,f232])).

fof(f229,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK2)
        | X0 = X1
        | ~ r2_hidden(X1,k3_relat_1(sK2))
        | ~ r2_hidden(X0,k3_relat_1(sK2))
        | ~ v6_relat_2(sK2)
        | r2_hidden(k4_tarski(X1,X0),sK2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f72,f130])).

fof(f72,plain,(
    ! [X4,X0,X3] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | X3 = X4
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v6_relat_2(X0)
      | r2_hidden(k4_tarski(X4,X3),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
            & sK3(X0) != sK4(X0)
            & r2_hidden(sK4(X0),k3_relat_1(X0))
            & r2_hidden(sK3(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0),sK3(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0),sK4(X0)),X0)
        & sK3(X0) != sK4(X0)
        & r2_hidden(sK4(X0),k3_relat_1(X0))
        & r2_hidden(sK3(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f146,plain,
    ( spl6_8
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f140,f129,f125,f143])).

fof(f140,plain,
    ( ! [X0] :
        ( ~ v2_wellord1(sK2)
        | k1_wellord1(sK2,X0) = k3_relat_1(k2_wellord1(sK2,k1_wellord1(sK2,X0))) )
    | ~ spl6_6 ),
    inference(resolution,[],[f93,f130])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v2_wellord1(X1)
      | k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(f135,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f70,f133])).

fof(f70,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f131,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f64,f129])).

fof(f64,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
    & sK0 != sK1
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f50])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
        & X0 != X1
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1)))
      & sK0 != sK1
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
      & X0 != X1
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
            & X0 != X1
            & r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ~ ( r4_wellord1(k2_wellord1(X2,k1_wellord1(X2,X0)),k2_wellord1(X2,k1_wellord1(X2,X1)))
          & X0 != X1
          & r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_wellord1)).

fof(f127,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f65,f125])).

fof(f65,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f123,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f66,f121])).

fof(f66,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f119,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f67,f117])).

fof(f67,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f68,f113])).

fof(f68,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f111,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f69,f109])).

fof(f69,plain,(
    r4_wellord1(k2_wellord1(sK2,k1_wellord1(sK2,sK0)),k2_wellord1(sK2,k1_wellord1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f51])).

%------------------------------------------------------------------------------
