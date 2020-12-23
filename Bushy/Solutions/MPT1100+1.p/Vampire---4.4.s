%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t5_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:45 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 570 expanded)
%              Number of leaves         :   58 ( 221 expanded)
%              Depth                    :   14
%              Number of atoms          :  549 (1524 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f662,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f132,f139,f146,f153,f161,f188,f199,f213,f221,f231,f243,f250,f259,f269,f284,f292,f306,f320,f340,f375,f382,f391,f435,f444,f452,f491,f513,f571,f572,f575,f602,f609,f623,f646,f648,f650,f651,f660])).

fof(f660,plain,
    ( ~ spl7_0
    | ~ spl7_2
    | spl7_7
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f659])).

fof(f659,plain,
    ( $false
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f658,f145])).

fof(f145,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK1))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl7_7
  <=> ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f658,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(sK1))
    | ~ spl7_0
    | ~ spl7_2
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f655,f333])).

fof(f333,plain,
    ( ! [X0] : k1_xboole_0 = k5_setfam_1(X0,k1_xboole_0)
    | ~ spl7_8 ),
    inference(forward_demodulation,[],[f330,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl7_8
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f330,plain,(
    ! [X0] : k5_setfam_1(X0,k1_xboole_0) = k3_tarski(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f171,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',redefinition_k5_setfam_1)).

fof(f171,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f84,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t3_subset)).

fof(f84,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t2_xboole_1)).

fof(f655,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(sK1),k1_xboole_0),u1_pre_topc(sK1))
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f131,f124,f84,f171,f95])).

fof(f95,plain,(
    ! [X2,X0] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tarski(X2,u1_pre_topc(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v2_pre_topc(X0)
      | r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
            & r1_tarski(sK4(X0),u1_pre_topc(X0))
            & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f72,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
          & r1_tarski(X1,u1_pre_topc(X0))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK4(X0)),u1_pre_topc(X0))
        & r1_tarski(sK4(X0),u1_pre_topc(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X1] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
              & r1_tarski(X1,u1_pre_topc(X0))
              & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X2] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X2),u1_pre_topc(X0))
                | ~ r1_tarski(X2,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0)
          | ? [X3] :
              ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              & r1_tarski(X3,u1_pre_topc(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        & ( ( sP0(X0)
            & ! [X3] :
                ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
                | ~ r1_tarski(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
          | ~ v2_pre_topc(X0) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( sP0(X0)
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f45,f61])).

fof(f61,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              | ~ r2_hidden(X2,u1_pre_topc(X0))
              | ~ r2_hidden(X1,u1_pre_topc(X0))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f45,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',d1_pre_topc)).

fof(f124,plain,
    ( v2_pre_topc(sK1)
    | ~ spl7_0 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_0
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_0])])).

fof(f131,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_2
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f651,plain,
    ( ~ spl7_15
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f235,f229,f183])).

fof(f183,plain,
    ( spl7_15
  <=> ~ v1_xboole_0(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f229,plain,
    ( spl7_22
  <=> r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f235,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK1))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f230,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t7_boole)).

fof(f230,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f229])).

fof(f650,plain,
    ( ~ spl7_14
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f649])).

fof(f649,plain,
    ( $false
    | ~ spl7_14
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f187,f235])).

fof(f187,plain,
    ( v1_xboole_0(u1_pre_topc(sK1))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl7_14
  <=> v1_xboole_0(u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f648,plain,
    ( ~ spl7_28
    | ~ spl7_30 ),
    inference(avatar_contradiction_clause,[],[f647])).

fof(f647,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_30 ),
    inference(subsumption_resolution,[],[f255,f273])).

fof(f273,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f268,f111])).

fof(f268,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl7_30
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f255,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f254,plain,
    ( spl7_28
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f646,plain,
    ( spl7_66
    | spl7_29
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f614,f600,f257,f644])).

fof(f644,plain,
    ( spl7_66
  <=> r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f257,plain,
    ( spl7_29
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f600,plain,
    ( spl7_60
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f614,plain,
    ( r2_hidden(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_29
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f258,f601,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t2_subset)).

fof(f601,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f600])).

fof(f258,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f257])).

fof(f623,plain,
    ( spl7_64
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f613,f600,f621])).

fof(f621,plain,
    ( spl7_64
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f613,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK1))
    | ~ spl7_60 ),
    inference(unit_resulting_resolution,[],[f601,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f609,plain,
    ( ~ spl7_63
    | spl7_13 ),
    inference(avatar_split_clause,[],[f298,f180,f607])).

fof(f607,plain,
    ( spl7_63
  <=> ~ r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f180,plain,
    ( spl7_13
  <=> ~ m1_subset_1(k1_xboole_0,u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f298,plain,
    ( ~ r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(u1_pre_topc(sK1))))
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f181,f100,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t4_subset)).

fof(f100,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(sK5(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f20,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f20,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',existence_m1_subset_1)).

fof(f181,plain,
    ( ~ m1_subset_1(k1_xboole_0,u1_pre_topc(sK1))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f180])).

fof(f602,plain,
    ( spl7_60
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f297,f229,f219,f600])).

fof(f219,plain,
    ( spl7_20
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f297,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f230,f220,f116])).

fof(f220,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f575,plain,
    ( spl7_40
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(avatar_split_clause,[],[f574,f450,f389,f318])).

fof(f318,plain,
    ( spl7_40
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f389,plain,
    ( spl7_48
  <=> v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f450,plain,
    ( spl7_54
  <=> k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_54])])).

fof(f574,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_48
    | ~ spl7_54 ),
    inference(forward_demodulation,[],[f390,f451])).

fof(f451,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_54 ),
    inference(avatar_component_clause,[],[f450])).

fof(f390,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_48 ),
    inference(avatar_component_clause,[],[f389])).

fof(f572,plain,(
    ~ spl7_42 ),
    inference(avatar_contradiction_clause,[],[f568])).

fof(f568,plain,
    ( $false
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f466,f500,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',antisymmetry_r2_hidden)).

fof(f500,plain,
    ( ! [X0] : r2_hidden(sK5(k1_xboole_0),X0)
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f457,f456,f105])).

fof(f456,plain,
    ( ! [X0] : m1_subset_1(sK5(k1_xboole_0),X0)
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f171,f339,f116])).

fof(f339,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl7_42
  <=> r2_hidden(sK5(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f457,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f171,f339,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t5_subset)).

fof(f466,plain,
    ( ! [X0] : r2_hidden(sK5(X0),X0)
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f100,f457,f105])).

fof(f571,plain,(
    ~ spl7_42 ),
    inference(avatar_contradiction_clause,[],[f566])).

fof(f566,plain,
    ( $false
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f466,f500,f103])).

fof(f513,plain,
    ( ~ spl7_59
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f460,f338,f511])).

fof(f511,plain,
    ( spl7_59
  <=> ~ r2_hidden(k1_xboole_0,sK5(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f460,plain,
    ( ~ r2_hidden(k1_xboole_0,sK5(k1_xboole_0))
    | ~ spl7_42 ),
    inference(unit_resulting_resolution,[],[f339,f103])).

fof(f491,plain,
    ( ~ spl7_57
    | spl7_47 ),
    inference(avatar_split_clause,[],[f423,f380,f489])).

fof(f489,plain,
    ( spl7_57
  <=> ~ r2_hidden(u1_pre_topc(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f380,plain,
    ( spl7_47
  <=> ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f423,plain,
    ( ~ r2_hidden(u1_pre_topc(sK1),k1_xboole_0)
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f171,f381,f116])).

fof(f381,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_47 ),
    inference(avatar_component_clause,[],[f380])).

fof(f452,plain,
    ( spl7_54
    | ~ spl7_48 ),
    inference(avatar_split_clause,[],[f402,f389,f450])).

fof(f402,plain,
    ( k1_xboole_0 = sK5(k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_48 ),
    inference(unit_resulting_resolution,[],[f390,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t6_boole)).

fof(f444,plain,
    ( ~ spl7_53
    | spl7_47 ),
    inference(avatar_split_clause,[],[f425,f380,f442])).

fof(f442,plain,
    ( spl7_53
  <=> ~ r2_hidden(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f425,plain,
    ( ~ r2_hidden(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f381,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t1_subset)).

fof(f435,plain,
    ( ~ spl7_51
    | spl7_47 ),
    inference(avatar_split_clause,[],[f422,f380,f433])).

fof(f433,plain,
    ( spl7_51
  <=> ~ r1_tarski(u1_pre_topc(sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f422,plain,
    ( ~ r1_tarski(u1_pre_topc(sK1),k1_xboole_0)
    | ~ spl7_47 ),
    inference(unit_resulting_resolution,[],[f381,f109])).

fof(f391,plain,
    ( spl7_48
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f383,f318,f389])).

fof(f383,plain,
    ( v1_xboole_0(sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f100,f345,f105])).

fof(f345,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f100,f319,f117])).

fof(f319,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f318])).

fof(f382,plain,
    ( ~ spl7_47
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f342,f318,f229,f380])).

fof(f342,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_22
    | ~ spl7_40 ),
    inference(unit_resulting_resolution,[],[f230,f319,f117])).

fof(f375,plain,
    ( ~ spl7_45
    | spl7_39 ),
    inference(avatar_split_clause,[],[f326,f312,f373])).

fof(f373,plain,
    ( spl7_45
  <=> ~ r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f312,plain,
    ( spl7_39
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f326,plain,
    ( ~ r2_hidden(k1_xboole_0,sK5(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl7_39 ),
    inference(unit_resulting_resolution,[],[f100,f313,f116])).

fof(f313,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f312])).

fof(f340,plain,
    ( spl7_42
    | spl7_41 ),
    inference(avatar_split_clause,[],[f321,f315,f338])).

fof(f315,plain,
    ( spl7_41
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f321,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | ~ spl7_41 ),
    inference(unit_resulting_resolution,[],[f100,f316,f105])).

fof(f316,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f315])).

fof(f320,plain,
    ( ~ spl7_39
    | spl7_40
    | spl7_37 ),
    inference(avatar_split_clause,[],[f307,f304,f318,f312])).

fof(f304,plain,
    ( spl7_37
  <=> ~ r2_hidden(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f307,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl7_37 ),
    inference(resolution,[],[f305,f105])).

fof(f305,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f304])).

fof(f306,plain,
    ( ~ spl7_37
    | spl7_13 ),
    inference(avatar_split_clause,[],[f295,f180,f304])).

fof(f295,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl7_13 ),
    inference(unit_resulting_resolution,[],[f181,f171,f116])).

fof(f292,plain,
    ( spl7_34
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f222,f219,f290])).

fof(f290,plain,
    ( spl7_34
  <=> r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f222,plain,
    ( r1_tarski(u1_pre_topc(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f220,f108])).

fof(f284,plain,
    ( ~ spl7_33
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f272,f267,f282])).

fof(f282,plain,
    ( spl7_33
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f272,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK1)),k1_xboole_0)
    | ~ spl7_30 ),
    inference(unit_resulting_resolution,[],[f268,f103])).

fof(f269,plain,
    ( spl7_30
    | spl7_29 ),
    inference(avatar_split_clause,[],[f260,f257,f267])).

fof(f260,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_29 ),
    inference(unit_resulting_resolution,[],[f171,f258,f105])).

fof(f259,plain,
    ( ~ spl7_29
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f252,f219,f197,f257])).

fof(f197,plain,
    ( spl7_16
  <=> r2_hidden(sK5(u1_pre_topc(sK1)),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f252,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f198,f220,f117])).

fof(f198,plain,
    ( r2_hidden(sK5(u1_pre_topc(sK1)),u1_pre_topc(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f197])).

fof(f250,plain,
    ( ~ spl7_27
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f234,f229,f248])).

fof(f248,plain,
    ( spl7_27
  <=> ~ r2_hidden(u1_pre_topc(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f234,plain,
    ( ~ r2_hidden(u1_pre_topc(sK1),u1_struct_0(sK1))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f230,f103])).

fof(f243,plain,
    ( spl7_24
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f232,f229,f241])).

fof(f241,plain,
    ( spl7_24
  <=> m1_subset_1(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f232,plain,
    ( m1_subset_1(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl7_22 ),
    inference(unit_resulting_resolution,[],[f230,f104])).

fof(f231,plain,
    ( spl7_22
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f223,f130,f123,f229])).

fof(f223,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK1))
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f131,f124,f94])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f221,plain,
    ( spl7_20
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f200,f130,f219])).

fof(f200,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f131,f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',dt_u1_pre_topc)).

fof(f213,plain,
    ( ~ spl7_19
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f204,f197,f211])).

fof(f211,plain,
    ( spl7_19
  <=> ~ r2_hidden(u1_pre_topc(sK1),sK5(u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f204,plain,
    ( ~ r2_hidden(u1_pre_topc(sK1),sK5(u1_pre_topc(sK1)))
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f198,f103])).

fof(f199,plain,
    ( spl7_16
    | spl7_15 ),
    inference(avatar_split_clause,[],[f189,f183,f197])).

fof(f189,plain,
    ( r2_hidden(sK5(u1_pre_topc(sK1)),u1_pre_topc(sK1))
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f100,f184,f105])).

fof(f184,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK1))
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f183])).

fof(f188,plain,
    ( ~ spl7_13
    | spl7_14
    | spl7_7 ),
    inference(avatar_split_clause,[],[f174,f144,f186,f180])).

fof(f174,plain,
    ( v1_xboole_0(u1_pre_topc(sK1))
    | ~ m1_subset_1(k1_xboole_0,u1_pre_topc(sK1))
    | ~ spl7_7 ),
    inference(resolution,[],[f105,f145])).

fof(f161,plain,
    ( spl7_10
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f154,f130,f123,f159])).

fof(f159,plain,
    ( spl7_10
  <=> sP0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f154,plain,
    ( sP0(sK1)
    | ~ spl7_0
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f131,f124,f96])).

fof(f96,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f153,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f83,f151])).

fof(f83,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t2_zfmisc_1)).

fof(f146,plain,(
    ~ spl7_7 ),
    inference(avatar_split_clause,[],[f82,f144])).

fof(f82,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK1))
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ? [X0] :
      ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',t5_pre_topc)).

fof(f139,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f118,f137])).

fof(f137,plain,
    ( spl7_4
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f118,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    l1_pre_topc(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f18,f78])).

fof(f78,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK6) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t5_pre_topc.p',existence_l1_pre_topc)).

fof(f132,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f81,f130])).

fof(f81,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

fof(f125,plain,(
    spl7_0 ),
    inference(avatar_split_clause,[],[f80,f123])).

fof(f80,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
