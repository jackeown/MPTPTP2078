%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t131_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:30 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 240 expanded)
%              Number of leaves         :   40 ( 100 expanded)
%              Depth                    :    9
%              Number of atoms          :  332 ( 642 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f74,f81,f88,f95,f112,f122,f134,f142,f159,f163,f176,f180,f187,f204,f218,f234,f254,f259,f266,f280])).

fof(f280,plain,
    ( ~ spl4_0
    | ~ spl4_4
    | ~ spl4_8
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_4
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f278,f80])).

fof(f80,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_4
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f278,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f277,f133])).

fof(f133,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_15
  <=> ~ v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f277,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ v1_partfun1(sK2,sK0)
    | ~ spl4_0
    | ~ spl4_8 ),
    inference(resolution,[],[f237,f94])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(sK2,X0,X1)
        | ~ v1_partfun1(sK2,X0) )
    | ~ spl4_0 ),
    inference(resolution,[],[f57,f66])).

fof(f66,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_0
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_partfun1(X2,X0)
      | v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',cc1_funct_2)).

fof(f266,plain,
    ( ~ spl4_41
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f257,f226,f264])).

fof(f264,plain,
    ( spl4_41
  <=> ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f226,plain,
    ( spl4_34
  <=> r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f257,plain,
    ( ~ r2_hidden(k2_zfmisc_1(sK0,sK1),sK3(sK2))
    | ~ spl4_34 ),
    inference(resolution,[],[f227,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',antisymmetry_r2_hidden)).

fof(f227,plain,
    ( r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f226])).

fof(f259,plain,
    ( ~ spl4_37
    | ~ spl4_34 ),
    inference(avatar_split_clause,[],[f258,f226,f229])).

fof(f229,plain,
    ( spl4_37
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f258,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_34 ),
    inference(resolution,[],[f227,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t7_boole)).

fof(f254,plain,
    ( spl4_38
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f241,f216,f65,f252])).

fof(f252,plain,
    ( spl4_38
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f216,plain,
    ( spl4_32
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f241,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl4_0
    | ~ spl4_32 ),
    inference(superposition,[],[f66,f217])).

fof(f217,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f216])).

fof(f234,plain,
    ( spl4_34
    | spl4_36
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f219,f202,f232,f226])).

fof(f232,plain,
    ( spl4_36
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f202,plain,
    ( spl4_30
  <=> m1_subset_1(sK3(sK2),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f219,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_30 ),
    inference(resolution,[],[f203,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t2_subset)).

fof(f203,plain,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f202])).

fof(f218,plain,
    ( spl4_32
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f209,f196,f120,f110,f216])).

fof(f110,plain,
    ( spl4_10
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f120,plain,
    ( spl4_12
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f196,plain,
    ( spl4_28
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f209,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f205,f121])).

fof(f121,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f205,plain,
    ( sK2 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_10
    | ~ spl4_28 ),
    inference(resolution,[],[f197,f114])).

fof(f114,plain,
    ( ! [X2] :
        ( ~ v1_xboole_0(X2)
        | sK3(k1_zfmisc_1(o_0_0_xboole_0)) = X2 )
    | ~ spl4_10 ),
    inference(resolution,[],[f111,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t8_boole)).

fof(f111,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f110])).

fof(f197,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f196])).

fof(f204,plain,
    ( spl4_28
    | spl4_30
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f191,f93,f202,f196])).

fof(f191,plain,
    ( m1_subset_1(sK3(sK2),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2)
    | ~ spl4_8 ),
    inference(resolution,[],[f189,f98])).

fof(f98,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',existence_m1_subset_1)).

fof(f189,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK2)
        | m1_subset_1(X2,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl4_8 ),
    inference(resolution,[],[f58,f94])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t4_subset)).

fof(f187,plain,
    ( ~ spl4_27
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f178,f168,f185])).

fof(f185,plain,
    ( spl4_27
  <=> ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f168,plain,
    ( spl4_22
  <=> r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f178,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)),sK2)
    | ~ spl4_22 ),
    inference(resolution,[],[f169,f51])).

fof(f169,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f168])).

fof(f180,plain,
    ( ~ spl4_25
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f179,f168,f171])).

fof(f171,plain,
    ( spl4_25
  <=> ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f179,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_22 ),
    inference(resolution,[],[f169,f55])).

fof(f176,plain,
    ( spl4_22
    | spl4_24
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f99,f93,f174,f168])).

fof(f174,plain,
    ( spl4_24
  <=> v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f99,plain,
    ( v1_xboole_0(k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r2_hidden(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_8 ),
    inference(resolution,[],[f53,f94])).

fof(f163,plain,
    ( ~ spl4_19
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f162,f157,f148])).

fof(f148,plain,
    ( spl4_19
  <=> ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f157,plain,
    ( spl4_20
  <=> r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f162,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(resolution,[],[f158,f55])).

fof(f158,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl4_18
    | spl4_20
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f126,f120,f157,f151])).

fof(f151,plain,
    ( spl4_18
  <=> v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f126,plain,
    ( r2_hidden(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f98,f121])).

fof(f142,plain,
    ( spl4_16
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f127,f120,f140])).

fof(f140,plain,
    ( spl4_16
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f127,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_12 ),
    inference(superposition,[],[f50,f121])).

fof(f134,plain,
    ( ~ spl4_1
    | ~ spl4_15
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f46,f90,f132,f62])).

fof(f62,plain,
    ( spl4_1
  <=> ~ v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f90,plain,
    ( spl4_9
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f46,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) )
    & v1_partfun1(sK2,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2) )
        & v1_partfun1(X2,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
      & v1_partfun1(sK2,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & v1_partfun1(X2,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2) )
      & v1_partfun1(X2,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
         => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t131_funct_2)).

fof(f122,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f115,f110,f120])).

fof(f115,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_10 ),
    inference(resolution,[],[f111,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f49,f48])).

fof(f48,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',d2_xboole_0)).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t6_boole)).

fof(f112,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f105,f72,f110])).

fof(f72,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f105,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f104,f98])).

fof(f104,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(resolution,[],[f103,f50])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f59,f73])).

fof(f73,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',t5_subset)).

fof(f95,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f44,f93])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f48,f86])).

fof(f86,plain,
    ( spl4_6
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f81,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f74,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f47,f72])).

fof(f47,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t131_funct_2.p',dt_o_0_0_xboole_0)).

fof(f67,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f43,f65])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
