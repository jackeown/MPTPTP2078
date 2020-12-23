%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t18_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:28 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 213 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   13
%              Number of atoms          :  231 ( 491 expanded)
%              Number of equality atoms :   34 (  84 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f114,f121,f131,f142,f168,f185,f192,f216,f247,f260,f278,f280,f282,f288])).

fof(f288,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f277,f120])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f277,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(trivial_inequality_removal,[],[f276])).

fof(f276,plain,
    ( u1_struct_0(sK0) != u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(superposition,[],[f184,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f88,f72])).

fof(f72,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',d4_subset_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',t25_subset_1)).

fof(f184,plain,
    ( u1_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_13
  <=> u1_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f282,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f271,f184])).

fof(f271,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f120,f100])).

fof(f280,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f273,f120])).

fof(f273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f184,f100])).

fof(f278,plain,
    ( ~ spl4_4
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f120,f184,f100])).

fof(f260,plain,
    ( ~ spl4_23
    | spl4_21 ),
    inference(avatar_split_clause,[],[f251,f242,f258])).

fof(f258,plain,
    ( spl4_23
  <=> ~ m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f242,plain,
    ( spl4_21
  <=> ~ v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f251,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f201,f243,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',t2_subset)).

fof(f243,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f242])).

fof(f201,plain,(
    ! [X0] : ~ r2_hidden(X0,X0) ),
    inference(unit_resulting_resolution,[],[f99,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f199,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',t5_subset)).

fof(f199,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f198,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',t4_subset)).

fof(f198,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f156,f85])).

fof(f156,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f85,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',antisymmetry_r2_hidden)).

fof(f99,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f76,f72])).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',dt_k2_subset_1)).

fof(f247,plain,
    ( ~ spl4_19
    | spl4_20
    | spl4_17 ),
    inference(avatar_split_clause,[],[f217,f214,f245,f239])).

fof(f239,plain,
    ( spl4_19
  <=> ~ m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f245,plain,
    ( spl4_20
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f214,plain,
    ( spl4_17
  <=> ~ r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f217,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | ~ spl4_17 ),
    inference(resolution,[],[f215,f85])).

fof(f215,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f214])).

fof(f216,plain,
    ( ~ spl4_17
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f206,f119,f214])).

fof(f206,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f120,f200])).

fof(f192,plain,
    ( spl4_14
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f177,f119,f190])).

fof(f190,plain,
    ( spl4_14
  <=> k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f177,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) = sK1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f120,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X1,X0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(condensation,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',idempotence_k4_subset_1)).

fof(f185,plain,
    ( ~ spl4_13
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f124,f105,f183])).

fof(f105,plain,
    ( spl4_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f124,plain,
    ( u1_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_0 ),
    inference(backward_demodulation,[],[f122,f71])).

fof(f71,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK1)) != k2_struct_0(sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f38,f63,f62])).

fof(f62,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( k4_subset_1(u1_struct_0(sK0),X1,k3_subset_1(u1_struct_0(sK0),X1)) != k2_struct_0(sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k4_subset_1(u1_struct_0(X0),sK1,k3_subset_1(u1_struct_0(X0),sK1)) != k2_struct_0(X0)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) != k2_struct_0(X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) = k2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',t18_pre_topc)).

fof(f122,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f106,f78])).

fof(f78,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',d3_struct_0)).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f105])).

fof(f168,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f160,f119,f166])).

fof(f166,plain,
    ( spl4_10
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f160,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f120,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',dt_k3_subset_1)).

fof(f142,plain,
    ( spl4_8
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f123,f112,f140])).

fof(f140,plain,
    ( spl4_8
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f112,plain,
    ( spl4_2
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f123,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f113,f78])).

fof(f113,plain,
    ( l1_struct_0(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f131,plain,
    ( spl4_6
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f122,f105,f129])).

fof(f129,plain,
    ( spl4_6
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f121,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f70,f119])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f114,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f97,f112])).

fof(f97,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f67])).

fof(f67,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t18_pre_topc.p',existence_l1_struct_0)).

fof(f107,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f69,f105])).

fof(f69,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
