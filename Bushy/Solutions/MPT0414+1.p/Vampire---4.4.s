%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t44_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:17 EDT 2019

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 400 expanded)
%              Number of leaves         :   42 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  373 (1196 expanded)
%              Number of equality atoms :   13 (  67 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f69,f76,f91,f109,f130,f142,f161,f165,f185,f202,f217,f264,f281,f294,f316,f335,f339,f346,f385,f409,f479,f480,f500,f508])).

fof(f508,plain,
    ( ~ spl5_4
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f505,f123])).

fof(f123,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_13
  <=> ~ r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f505,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f502])).

fof(f502,plain,
    ( r1_tarski(sK1,sK2)
    | r1_tarski(sK1,sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f257,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',d3_tarski)).

fof(f257,plain,
    ( ! [X5] :
        ( ~ r2_hidden(sK3(X5,sK2),sK1)
        | r1_tarski(X5,sK2) )
    | ~ spl5_4 ),
    inference(resolution,[],[f177,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f177,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,sK2)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f144,f33])).

fof(f33,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | r2_hidden(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(X0))
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',t44_setfam_1)).

fof(f144,plain,
    ( ! [X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f43,f75])).

fof(f75,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',t4_subset)).

fof(f500,plain,
    ( ~ spl5_53
    | ~ spl5_2
    | spl5_27 ),
    inference(avatar_split_clause,[],[f453,f215,f67,f498])).

fof(f498,plain,
    ( spl5_53
  <=> ~ m1_subset_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f67,plain,
    ( spl5_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f215,plain,
    ( spl5_27
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f453,plain,
    ( ~ m1_subset_1(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(duplicate_literal_removal,[],[f451])).

fof(f451,plain,
    ( ~ m1_subset_1(sK1,sK2)
    | ~ m1_subset_1(sK1,sK2)
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(resolution,[],[f299,f243])).

fof(f243,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f242,f216])).

fof(f216,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f215])).

fof(f242,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | v1_xboole_0(sK2)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f171,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',t2_subset)).

fof(f171,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK1) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,sK1) )
    | ~ spl5_2 ),
    inference(resolution,[],[f143,f32])).

fof(f32,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK0))
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f143,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl5_2 ),
    inference(resolution,[],[f43,f68])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f299,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ m1_subset_1(X1,sK2) )
    | ~ spl5_2
    | ~ spl5_27 ),
    inference(resolution,[],[f243,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',antisymmetry_r2_hidden)).

fof(f480,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f476,f67,f125])).

fof(f125,plain,
    ( spl5_14
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f476,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f468])).

fof(f468,plain,
    ( r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f241,f47])).

fof(f241,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK2,X0),sK1)
        | r1_tarski(sK2,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f171,f46])).

fof(f479,plain,
    ( ~ spl5_2
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f478])).

fof(f478,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f476,f129])).

fof(f129,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl5_15
  <=> ~ r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f409,plain,
    ( ~ spl5_51
    | spl5_25
    | spl5_47 ),
    inference(avatar_split_clause,[],[f366,f344,f200,f407])).

fof(f407,plain,
    ( spl5_51
  <=> ~ m1_subset_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f200,plain,
    ( spl5_25
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f344,plain,
    ( spl5_47
  <=> ~ r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f366,plain,
    ( ~ m1_subset_1(sK2,sK1)
    | ~ spl5_25
    | ~ spl5_47 ),
    inference(subsumption_resolution,[],[f365,f201])).

fof(f201,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f365,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK1)
    | ~ spl5_47 ),
    inference(resolution,[],[f345,f48])).

fof(f345,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f344])).

fof(f385,plain,
    ( ~ spl5_49
    | ~ spl5_2
    | spl5_27
    | spl5_47 ),
    inference(avatar_split_clause,[],[f364,f344,f215,f67,f383])).

fof(f383,plain,
    ( spl5_49
  <=> ~ m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f364,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl5_2
    | ~ spl5_27
    | ~ spl5_47 ),
    inference(resolution,[],[f345,f243])).

fof(f346,plain,
    ( ~ spl5_47
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f325,f74,f344])).

fof(f325,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_4 ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK2,sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f253,f177])).

fof(f253,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK2,X2)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f177,f50])).

fof(f339,plain,
    ( ~ spl5_41
    | spl5_44
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f175,f74,f337,f330])).

fof(f330,plain,
    ( spl5_41
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f337,plain,
    ( spl5_44
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f175,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | ~ r2_hidden(X5,X4)
        | ~ v1_xboole_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f144,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',t5_subset)).

fof(f335,plain,
    ( ~ spl5_41
    | spl5_42
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f169,f67,f333,f330])).

fof(f333,plain,
    ( spl5_42
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X5,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f169,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK2)
        | ~ r2_hidden(X5,X4)
        | ~ v1_xboole_0(sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f143,f42])).

fof(f316,plain,
    ( spl5_36
    | ~ spl5_39
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f150,f140,f314,f308])).

fof(f308,plain,
    ( spl5_36
  <=> k1_zfmisc_1(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f314,plain,
    ( spl5_39
  <=> ~ r1_tarski(k1_zfmisc_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f140,plain,
    ( spl5_16
  <=> r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f150,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),sK1)
    | k1_zfmisc_1(sK0) = sK1
    | ~ spl5_16 ),
    inference(resolution,[],[f141,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',d10_xboole_0)).

fof(f141,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f294,plain,
    ( spl5_32
    | ~ spl5_35
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f148,f107,f292,f286])).

fof(f286,plain,
    ( spl5_32
  <=> k1_zfmisc_1(sK0) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f292,plain,
    ( spl5_35
  <=> ~ r1_tarski(k1_zfmisc_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f107,plain,
    ( spl5_10
  <=> r1_tarski(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f148,plain,
    ( ~ r1_tarski(k1_zfmisc_1(sK0),sK2)
    | k1_zfmisc_1(sK0) = sK2
    | ~ spl5_10 ),
    inference(resolution,[],[f108,f40])).

fof(f108,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f281,plain,
    ( ~ spl5_31
    | spl5_26
    | spl5_9 ),
    inference(avatar_split_clause,[],[f151,f86,f212,f279])).

fof(f279,plain,
    ( spl5_31
  <=> ~ m1_subset_1(sK4(k1_zfmisc_1(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f212,plain,
    ( spl5_26
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f86,plain,
    ( spl5_9
  <=> ~ r2_hidden(sK4(k1_zfmisc_1(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f151,plain,
    ( v1_xboole_0(sK2)
    | ~ m1_subset_1(sK4(k1_zfmisc_1(sK0)),sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f87,f48])).

fof(f87,plain,
    ( ~ r2_hidden(sK4(k1_zfmisc_1(sK0)),sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f264,plain,
    ( ~ spl5_29
    | spl5_24
    | spl5_7 ),
    inference(avatar_split_clause,[],[f113,f83,f197,f262])).

fof(f262,plain,
    ( spl5_29
  <=> ~ m1_subset_1(sK4(k1_zfmisc_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f197,plain,
    ( spl5_24
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f83,plain,
    ( spl5_7
  <=> ~ r2_hidden(sK4(k1_zfmisc_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f113,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK4(k1_zfmisc_1(sK0)),sK1)
    | ~ spl5_7 ),
    inference(resolution,[],[f48,f84])).

fof(f84,plain,
    ( ~ r2_hidden(sK4(k1_zfmisc_1(sK0)),sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f83])).

fof(f217,plain,
    ( ~ spl5_27
    | spl5_15 ),
    inference(avatar_split_clause,[],[f195,f128,f215])).

fof(f195,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl5_15 ),
    inference(resolution,[],[f100,f129])).

fof(f100,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',t7_boole)).

fof(f202,plain,
    ( ~ spl5_25
    | spl5_13 ),
    inference(avatar_split_clause,[],[f194,f122,f200])).

fof(f194,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl5_13 ),
    inference(resolution,[],[f100,f123])).

fof(f185,plain,
    ( spl5_6
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f78,f86,f80])).

fof(f80,plain,
    ( spl5_6
  <=> r2_hidden(sK4(k1_zfmisc_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f78,plain,
    ( ~ r2_hidden(sK4(k1_zfmisc_1(sK0)),sK2)
    | r2_hidden(sK4(k1_zfmisc_1(sK0)),sK1) ),
    inference(resolution,[],[f53,f32])).

fof(f53,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',existence_m1_subset_1)).

fof(f165,plain,
    ( ~ spl5_19
    | spl5_22
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f132,f74,f163,f156])).

fof(f156,plain,
    ( spl5_19
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f163,plain,
    ( spl5_22
  <=> ! [X1] : ~ r2_hidden(X1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f132,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK1)
        | ~ v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl5_4 ),
    inference(resolution,[],[f42,f75])).

fof(f161,plain,
    ( ~ spl5_19
    | spl5_20
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f131,f67,f159,f156])).

fof(f159,plain,
    ( spl5_20
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ v1_xboole_0(k1_zfmisc_1(sK0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f68])).

fof(f142,plain,
    ( spl5_16
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f95,f74,f140])).

fof(f95,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f52,f75])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/setfam_1__t44_setfam_1.p',t3_subset)).

fof(f130,plain,
    ( ~ spl5_13
    | ~ spl5_15
    | spl5_1 ),
    inference(avatar_split_clause,[],[f115,f60,f128,f122])).

fof(f60,plain,
    ( spl5_1
  <=> sK1 != sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f115,plain,
    ( ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK1,sK2)
    | ~ spl5_1 ),
    inference(extensionality_resolution,[],[f40,f61])).

fof(f61,plain,
    ( sK1 != sK2
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f109,plain,
    ( spl5_10
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f94,f67,f107])).

fof(f94,plain,
    ( r1_tarski(sK2,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f52,f68])).

fof(f91,plain,
    ( ~ spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f77,f89,f83])).

fof(f89,plain,
    ( spl5_8
  <=> r2_hidden(sK4(k1_zfmisc_1(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f77,plain,
    ( r2_hidden(sK4(k1_zfmisc_1(sK0)),sK2)
    | ~ r2_hidden(sK4(k1_zfmisc_1(sK0)),sK1) ),
    inference(resolution,[],[f53,f33])).

fof(f76,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f62,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
