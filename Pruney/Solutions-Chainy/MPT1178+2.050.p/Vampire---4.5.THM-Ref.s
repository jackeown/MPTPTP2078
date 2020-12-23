%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 239 expanded)
%              Number of leaves         :   31 ( 110 expanded)
%              Depth                    :   11
%              Number of atoms          :  470 ( 946 expanded)
%              Number of equality atoms :   40 (  99 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f153,f158,f234,f267,f286,f437,f515])).

fof(f515,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | spl7_11
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9
    | spl7_11
    | spl7_15 ),
    inference(subsumption_resolution,[],[f513,f77])).

fof(f77,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f513,plain,
    ( ~ r1_xboole_0(k4_orders_2(sK0,sK1),k1_xboole_0)
    | ~ spl7_8
    | ~ spl7_9
    | spl7_11
    | spl7_15 ),
    inference(forward_demodulation,[],[f512,f201])).

fof(f201,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f89,f77,f91,f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f91,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).

fof(f512,plain,
    ( ~ r1_xboole_0(k4_orders_2(sK0,sK1),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_8
    | ~ spl7_9
    | spl7_11
    | spl7_15 ),
    inference(forward_demodulation,[],[f489,f157])).

fof(f157,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl7_9
  <=> k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f489,plain,
    ( ~ r1_xboole_0(k4_orders_2(sK0,sK1),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k2_tarski(k1_xboole_0,k1_xboole_0)))
    | ~ spl7_8
    | spl7_11
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f233,f152,f436,f197])).

fof(f197,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_xboole_0(X5,k4_xboole_0(X6,k2_tarski(X4,X4)))
      | ~ r1_tarski(X5,X6)
      | r2_hidden(X4,X5)
      | v1_xboole_0(X5) ) ),
    inference(resolution,[],[f110,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f102,f81])).

fof(f81,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_zfmisc_1)).

fof(f436,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl7_15
  <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f152,plain,
    ( r1_tarski(k4_orders_2(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_8
  <=> r1_tarski(k4_orders_2(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f233,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl7_11
  <=> v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f437,plain,
    ( ~ spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_13 ),
    inference(avatar_split_clause,[],[f311,f283,f139,f134,f129,f124,f119,f114,f434])).

fof(f114,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f119,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f124,plain,
    ( spl7_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f129,plain,
    ( spl7_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f134,plain,
    ( spl7_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f139,plain,
    ( spl7_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f283,plain,
    ( spl7_13
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f311,plain,
    ( ~ r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | spl7_13 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f141,f285,f112])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X4,X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(f285,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl7_13 ),
    inference(avatar_component_clause,[],[f283])).

fof(f141,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f136,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f134])).

fof(f131,plain,
    ( v5_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f126,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f121,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f116,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f114])).

fof(f286,plain,
    ( ~ spl7_13
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f269,f264,f139,f134,f129,f124,f119,f114,f283])).

fof(f264,plain,
    ( spl7_12
  <=> m2_orders_2(sK6(sK0,sK1),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f269,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_12 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f77,f141,f266,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ r1_xboole_0(X2,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ~ r1_xboole_0(X2,X3)
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ~ r1_xboole_0(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).

fof(f266,plain,
    ( m2_orders_2(sK6(sK0,sK1),sK0,sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f264])).

fof(f267,plain,
    ( spl7_12
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f214,f139,f134,f129,f124,f119,f114,f264])).

fof(f214,plain,
    ( m2_orders_2(sK6(sK0,sK1),sK0,sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f141,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(sK6(X0,X1),X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK6(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK6(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f234,plain,
    ( ~ spl7_11
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f213,f139,f134,f129,f124,f119,f114,f231])).

fof(f213,plain,
    ( ~ v1_xboole_0(k4_orders_2(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f141,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f158,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f106,f155])).

fof(f106,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f75,f81])).

fof(f75,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f153,plain,
    ( spl7_8
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f148,f144,f150])).

fof(f144,plain,
    ( spl7_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f148,plain,
    ( r1_tarski(k4_orders_2(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_7 ),
    inference(superposition,[],[f80,f146])).

fof(f146,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f80,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f147,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f74,f144])).

fof(f74,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f54,f53])).

fof(f53,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

% (26473)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f54,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f142,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f73,f139])).

fof(f73,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f137,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f72,f134])).

fof(f72,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f132,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f71,f129])).

fof(f71,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f127,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f70,f124])).

fof(f70,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f122,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f69,f119])).

fof(f69,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f117,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f68,f114])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (26485)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.48  % (26493)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (26493)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (26474)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (26501)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f528,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f117,f122,f127,f132,f137,f142,f147,f153,f158,f234,f267,f286,f437,f515])).
% 0.20/0.51  fof(f515,plain,(
% 0.20/0.51    ~spl7_8 | ~spl7_9 | spl7_11 | spl7_15),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f514])).
% 0.20/0.51  fof(f514,plain,(
% 0.20/0.51    $false | (~spl7_8 | ~spl7_9 | spl7_11 | spl7_15)),
% 0.20/0.51    inference(subsumption_resolution,[],[f513,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.51  fof(f513,plain,(
% 0.20/0.51    ~r1_xboole_0(k4_orders_2(sK0,sK1),k1_xboole_0) | (~spl7_8 | ~spl7_9 | spl7_11 | spl7_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f512,f201])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f89,f77,f91,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | X1 = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (X1 = X2 | ~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3))),
% 0.20/0.51    inference(flattening,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (X1 = X2 | (~r1_xboole_0(X3,X1) | ~r1_xboole_0(X2,X0) | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_xboole_1)).
% 0.20/0.52  fof(f512,plain,(
% 0.20/0.52    ~r1_xboole_0(k4_orders_2(sK0,sK1),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) | (~spl7_8 | ~spl7_9 | spl7_11 | spl7_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f489,f157])).
% 0.20/0.52  fof(f157,plain,(
% 0.20/0.52    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0) | ~spl7_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f155])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    spl7_9 <=> k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.52  fof(f489,plain,(
% 0.20/0.52    ~r1_xboole_0(k4_orders_2(sK0,sK1),k4_xboole_0(k1_zfmisc_1(k1_xboole_0),k2_tarski(k1_xboole_0,k1_xboole_0))) | (~spl7_8 | spl7_11 | spl7_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f233,f152,f436,f197])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X6,X4,X5] : (~r1_xboole_0(X5,k4_xboole_0(X6,k2_tarski(X4,X4))) | ~r1_tarski(X5,X6) | r2_hidden(X4,X5) | v1_xboole_0(X5)) )),
% 0.20/0.52    inference(resolution,[],[f110,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.52    inference(flattening,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k2_tarski(X2,X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f102,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_zfmisc_1)).
% 0.20/0.52  fof(f436,plain,(
% 0.20/0.52    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | spl7_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f434])).
% 0.20/0.52  fof(f434,plain,(
% 0.20/0.52    spl7_15 <=> r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    r1_tarski(k4_orders_2(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl7_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    spl7_8 <=> r1_tarski(k4_orders_2(sK0,sK1),k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | spl7_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f231])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    spl7_11 <=> v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.52  fof(f437,plain,(
% 0.20/0.52    ~spl7_15 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f311,f283,f139,f134,f129,f124,f119,f114,f434])).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    spl7_1 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl7_2 <=> v3_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    spl7_3 <=> v4_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.52  fof(f129,plain,(
% 0.20/0.52    spl7_4 <=> v5_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    spl7_5 <=> l1_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    spl7_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.52  fof(f283,plain,(
% 0.20/0.52    spl7_13 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.52  fof(f311,plain,(
% 0.20/0.52    ~r2_hidden(k1_xboole_0,k4_orders_2(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | spl7_13)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f141,f285,f112])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X4,X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f57,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(rectify,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.20/0.52  fof(f285,plain,(
% 0.20/0.52    ~m2_orders_2(k1_xboole_0,sK0,sK1) | spl7_13),
% 0.20/0.52    inference(avatar_component_clause,[],[f283])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl7_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f139])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    l1_orders_2(sK0) | ~spl7_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f134])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    v5_orders_2(sK0) | ~spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f129])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    v4_orders_2(sK0) | ~spl7_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f124])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    v3_orders_2(sK0) | ~spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f119])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    ~v2_struct_0(sK0) | spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f114])).
% 0.20/0.52  fof(f286,plain,(
% 0.20/0.52    ~spl7_13 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f269,f264,f139,f134,f129,f124,f119,f114,f283])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    spl7_12 <=> m2_orders_2(sK6(sK0,sK1),sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.52  fof(f269,plain,(
% 0.20/0.52    ~m2_orders_2(k1_xboole_0,sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_12)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f77,f141,f266,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~r1_xboole_0(X2,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (~r1_xboole_0(X2,X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => ~r1_xboole_0(X2,X3)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_orders_2)).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    m2_orders_2(sK6(sK0,sK1),sK0,sK1) | ~spl7_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f264])).
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    spl7_12 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f214,f139,f134,f129,f124,f119,f114,f264])).
% 0.20/0.52  fof(f214,plain,(
% 0.20/0.52    m2_orders_2(sK6(sK0,sK1),sK0,sK1) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f141,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK6(X0,X1),X0,X1) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ! [X0,X1] : (m2_orders_2(sK6(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK6(X0,X1),X0,X1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ~spl7_11 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f213,f139,f134,f129,f124,f119,f114,f231])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    ~v1_xboole_0(k4_orders_2(sK0,sK1)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f116,f121,f126,f131,f136,f141,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    spl7_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f106,f155])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    k1_zfmisc_1(k1_xboole_0) = k2_tarski(k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    inference(definition_unfolding,[],[f75,f81])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,axiom,(
% 0.20/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    spl7_8 | ~spl7_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f148,f144,f150])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl7_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    r1_tarski(k4_orders_2(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) | ~spl7_7),
% 0.20/0.52    inference(superposition,[],[f80,f146])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl7_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f144])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    spl7_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f74,f144])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f30,f54,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  % (26473)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f25])).
% 0.20/0.52  fof(f25,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    spl7_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f73,f139])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f55])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    spl7_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f72,f134])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    l1_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f132,plain,(
% 0.20/0.53    spl7_4),
% 0.20/0.53    inference(avatar_split_clause,[],[f71,f129])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    v5_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    spl7_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f70,f124])).
% 0.20/0.53  fof(f70,plain,(
% 0.20/0.53    v4_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f122,plain,(
% 0.20/0.53    spl7_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f69,f119])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    v3_orders_2(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    ~spl7_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f68,f114])).
% 0.20/0.53  fof(f68,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f55])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (26493)------------------------------
% 0.20/0.53  % (26493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (26493)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (26493)Memory used [KB]: 11001
% 0.20/0.53  % (26493)Time elapsed: 0.100 s
% 0.20/0.53  % (26493)------------------------------
% 0.20/0.53  % (26493)------------------------------
% 0.20/0.53  % (26481)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (26472)Success in time 0.172 s
%------------------------------------------------------------------------------
