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
% DateTime   : Thu Dec  3 12:59:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 308 expanded)
%              Number of leaves         :   48 ( 157 expanded)
%              Depth                    :    8
%              Number of atoms          :  459 (1507 expanded)
%              Number of equality atoms :   97 ( 184 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f338,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f103,f111,f126,f127,f137,f234,f245,f246,f247,f248,f281,f282,f289,f296,f303,f304,f312,f313,f316,f317,f336,f337])).

fof(f337,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)
    | ~ r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f336,plain,
    ( spl9_20
    | spl9_21
    | spl9_22
    | spl9_23
    | spl9_43
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f329,f67,f332,f167,f163,f159,f155])).

fof(f155,plain,
    ( spl9_20
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f159,plain,
    ( spl9_21
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f163,plain,
    ( spl9_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f167,plain,
    ( spl9_23
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f332,plain,
    ( spl9_43
  <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f67,plain,
    ( spl9_6
  <=> m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f329,plain,
    ( k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_6 ),
    inference(resolution,[],[f43,f69])).

fof(f69,plain,
    ( m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f33,f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f32,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
            & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
            & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
            & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) )
          | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) )
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ~ ( ~ ! [X4] :
              ( m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
             => ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
                & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
                & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
                & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) ) )
        & k1_xboole_0 != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

fof(f317,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f316,plain,
    ( k1_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f313,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f312,plain,
    ( spl9_20
    | spl9_21
    | spl9_22
    | spl9_23
    | spl9_42
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f306,f67,f308,f167,f163,f159,f155])).

fof(f308,plain,
    ( spl9_42
  <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f306,plain,
    ( k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_6 ),
    inference(resolution,[],[f42,f69])).

fof(f42,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f34,f37])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4)))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f304,plain,
    ( spl9_20
    | spl9_21
    | spl9_22
    | spl9_23
    | spl9_24
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f300,f67,f171,f167,f163,f159,f155])).

fof(f171,plain,
    ( spl9_24
  <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f300,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_6 ),
    inference(resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f36,f37])).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4)
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f303,plain,
    ( spl9_20
    | spl9_21
    | spl9_22
    | spl9_23
    | spl9_25
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f299,f67,f177,f167,f163,f159,f155])).

fof(f177,plain,
    ( spl9_25
  <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).

fof(f299,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | ~ spl9_6 ),
    inference(resolution,[],[f69,f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3))
      | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f35,f37])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4))
      | ~ m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))
      | k1_xboole_0 = X3
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f296,plain,
    ( ~ spl9_41
    | ~ spl9_9
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f291,f277,f82,f293])).

fof(f293,plain,
    ( spl9_41
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f82,plain,
    ( spl9_9
  <=> m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f277,plain,
    ( spl9_39
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f291,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl9_9
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f84,f279,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f279,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f277])).

fof(f84,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK1))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f289,plain,
    ( ~ spl9_40
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(avatar_split_clause,[],[f284,f272,f87,f286])).

fof(f286,plain,
    ( spl9_40
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f87,plain,
    ( spl9_10
  <=> m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f272,plain,
    ( spl9_38
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f284,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_10
    | ~ spl9_38 ),
    inference(unit_resulting_resolution,[],[f89,f274,f31])).

fof(f274,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f272])).

fof(f89,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f282,plain,
    ( spl9_38
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f265,f107,f272])).

fof(f107,plain,
    ( spl9_13
  <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f265,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)
    | ~ spl9_13 ),
    inference(resolution,[],[f109,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k1_mcart_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f109,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f107])).

fof(f281,plain,
    ( spl9_39
    | ~ spl9_13 ),
    inference(avatar_split_clause,[],[f264,f107,f277])).

fof(f264,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)
    | ~ spl9_13 ),
    inference(resolution,[],[f109,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | r2_hidden(k2_mcart_1(X0),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f248,plain,
    ( k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(sK8))
    | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f247,plain,
    ( k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(sK8)
    | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k2_mcart_1(sK8),sK7) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f246,plain,
    ( k1_xboole_0 != sK3
    | v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f245,plain,
    ( ~ spl9_11
    | ~ spl9_12
    | ~ spl9_34 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f101,f235,f30])).

fof(f235,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK6)
    | ~ spl9_11
    | ~ spl9_34 ),
    inference(unit_resulting_resolution,[],[f94,f233,f31])).

fof(f233,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_34 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl9_34
  <=> m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f94,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl9_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f101,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl9_12
  <=> r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f234,plain,
    ( spl9_34
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f224,f163,f77,f231])).

fof(f77,plain,
    ( spl9_8
  <=> m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f224,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_8
    | ~ spl9_22 ),
    inference(backward_demodulation,[],[f79,f165])).

fof(f165,plain,
    ( k1_xboole_0 = sK2
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f163])).

fof(f79,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(sK2))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f137,plain,
    ( ~ spl9_16
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f131,f122,f72,f134])).

fof(f134,plain,
    ( spl9_16
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f72,plain,
    ( spl9_7
  <=> m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f122,plain,
    ( spl9_15
  <=> r2_hidden(k2_mcart_1(sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f131,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl9_7
    | ~ spl9_15 ),
    inference(unit_resulting_resolution,[],[f124,f74,f31])).

fof(f74,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(sK3))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f72])).

fof(f124,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f127,plain,
    ( spl9_14
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f115,f99,f117])).

fof(f117,plain,
    ( spl9_14
  <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f115,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)
    | ~ spl9_12 ),
    inference(resolution,[],[f30,f101])).

fof(f126,plain,
    ( spl9_15
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f114,f62,f122])).

fof(f62,plain,
    ( spl9_5
  <=> r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f114,plain,
    ( r2_hidden(k2_mcart_1(sK8),sK7)
    | ~ spl9_5 ),
    inference(resolution,[],[f30,f64])).

% (3766)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
fof(f64,plain,
    ( r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f111,plain,
    ( spl9_13
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f105,f99,f107])).

fof(f105,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))
    | ~ spl9_12 ),
    inference(resolution,[],[f101,f29])).

fof(f103,plain,
    ( spl9_12
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f97,f62,f99])).

fof(f97,plain,
    ( r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))
    | ~ spl9_5 ),
    inference(resolution,[],[f29,f64])).

fof(f95,plain,(
    spl9_11 ),
    inference(avatar_split_clause,[],[f27,f92])).

fof(f27,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f20,f87])).

fof(f20,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
    & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
    & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))
    & m1_subset_1(sK7,k1_zfmisc_1(sK3))
    & m1_subset_1(sK6,k1_zfmisc_1(sK2))
    & m1_subset_1(sK5,k1_zfmisc_1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f10,f18,f17,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ? [X7] :
                    ( ? [X8] :
                        ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                        & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                        & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                    & m1_subset_1(X7,k1_zfmisc_1(X3)) )
                & m1_subset_1(X6,k1_zfmisc_1(X2)) )
            & m1_subset_1(X5,k1_zfmisc_1(X1)) )
        & m1_subset_1(X4,k1_zfmisc_1(X0)) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                      & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
              & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
          & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK4,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ? [X7] :
                ( ? [X8] :
                    ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                      | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                      | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5)
                      | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                    & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7))
                    & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
                & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
            & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
        & m1_subset_1(X5,k1_zfmisc_1(sK1)) )
   => ( ? [X6] :
          ( ? [X7] :
              ( ? [X8] :
                  ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                  & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                  & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
              & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
          & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X6] :
        ( ? [X7] :
            ( ? [X8] :
                ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                  | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6)
                  | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                  | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
                & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7))
                & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
            & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
        & m1_subset_1(X6,k1_zfmisc_1(sK2)) )
   => ( ? [X7] :
          ( ? [X8] :
              ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
                | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
                | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
                | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
              & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
              & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
          & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
      & m1_subset_1(sK6,k1_zfmisc_1(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X7] :
        ( ? [X8] :
            ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7)
              | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
              | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
              | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
            & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7))
            & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
        & m1_subset_1(X7,k1_zfmisc_1(sK3)) )
   => ( ? [X8] :
          ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
            | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
            | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
            | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
          & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
          & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
      & m1_subset_1(sK7,k1_zfmisc_1(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X8] :
        ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7)
          | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6)
          | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5)
          | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4) )
        & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
        & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) )
   => ( ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
        | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
        | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
        | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) )
      & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))
      & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ? [X5] :
          ( ? [X6] :
              ( ? [X7] :
                  ( ? [X8] :
                      ( ( ~ r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                        | ~ r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                        | ~ r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                        | ~ r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) )
                      & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                      & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) )
                  & m1_subset_1(X7,k1_zfmisc_1(X3)) )
              & m1_subset_1(X6,k1_zfmisc_1(X2)) )
          & m1_subset_1(X5,k1_zfmisc_1(X1)) )
      & m1_subset_1(X4,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k1_zfmisc_1(X0))
       => ! [X5] :
            ( m1_subset_1(X5,k1_zfmisc_1(X1))
           => ! [X6] :
                ( m1_subset_1(X6,k1_zfmisc_1(X2))
               => ! [X7] :
                    ( m1_subset_1(X7,k1_zfmisc_1(X3))
                   => ! [X8] :
                        ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                       => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                         => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                            & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                            & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                            & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

% (3773)Refutation not found, incomplete strategy% (3773)------------------------------
% (3773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f7,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(X0))
     => ! [X5] :
          ( m1_subset_1(X5,k1_zfmisc_1(X1))
         => ! [X6] :
              ( m1_subset_1(X6,k1_zfmisc_1(X2))
             => ! [X7] :
                  ( m1_subset_1(X7,k1_zfmisc_1(X3))
                 => ! [X8] :
                      ( m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))
                     => ( r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))
                       => ( r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7)
                          & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6)
                          & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5)
                          & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

fof(f85,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f21,f82])).

fof(f21,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f22,f77])).

fof(f22,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f75,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f23,f72])).

fof(f23,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f70,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) ),
    inference(definition_unfolding,[],[f24,f37])).

fof(f24,plain,(
    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f38,f62])).

fof(f38,plain,(
    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) ),
    inference(definition_unfolding,[],[f25,f37])).

fof(f25,plain,(
    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f19])).

fof(f60,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f26,f57,f53,f49,f45])).

fof(f45,plain,
    ( spl9_1
  <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f49,plain,
    ( spl9_2
  <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f53,plain,
    ( spl9_3
  <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f57,plain,
    ( spl9_4
  <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f26,plain,
    ( ~ r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)
    | ~ r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)
    | ~ r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)
    | ~ r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (3765)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (3763)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (3768)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (3774)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (3769)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (3772)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (3771)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (3768)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (3773)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (3770)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (3778)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (3779)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (3764)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f338,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f103,f111,f126,f127,f137,f234,f245,f246,f247,f248,f281,f282,f289,f296,f303,f304,f312,f313,f316,f317,f336,f337])).
% 0.21/0.49  fof(f337,plain,(
% 0.21/0.49    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) != k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4) | ~r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f336,plain,(
% 0.21/0.49    spl9_20 | spl9_21 | spl9_22 | spl9_23 | spl9_43 | ~spl9_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f329,f67,f332,f167,f163,f159,f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl9_20 <=> k1_xboole_0 = sK0),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl9_21 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    spl9_22 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.21/0.49  fof(f167,plain,(
% 0.21/0.49    spl9_23 <=> k1_xboole_0 = sK3),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.21/0.49  fof(f332,plain,(
% 0.21/0.49    spl9_43 <=> k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    spl9_6 <=> m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.49  fof(f329,plain,(
% 0.21/0.49    k8_mcart_1(sK0,sK1,sK2,sK3,sK8) = k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl9_6),
% 0.21/0.49    inference(resolution,[],[f43,f69])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3)) | ~spl9_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f67])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f33,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) )),
% 0.21/0.49    inference(definition_unfolding,[],[f32,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k2_zfmisc_1(k3_zfmisc_1(X0,X1,X2),X3)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (! [X4] : ((k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4)))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : ~(~! [X4] : (m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) => (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) & k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) & k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) & k8_mcart_1(X0,X1,X2,X3,X4) = k1_mcart_1(k1_mcart_1(k1_mcart_1(X4))))) & k1_xboole_0 != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).
% 0.21/0.49  fof(f317,plain,(
% 0.21/0.49    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    k1_xboole_0 != sK0 | v1_xboole_0(sK0) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f313,plain,(
% 0.21/0.49    k1_xboole_0 != sK1 | ~v1_xboole_0(k1_xboole_0) | v1_xboole_0(sK1)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f312,plain,(
% 0.21/0.49    spl9_20 | spl9_21 | spl9_22 | spl9_23 | spl9_42 | ~spl9_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f306,f67,f308,f167,f163,f159,f155])).
% 0.21/0.49  fof(f308,plain,(
% 0.21/0.49    spl9_42 <=> k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 0.21/0.49  fof(f306,plain,(
% 0.21/0.49    k9_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl9_6),
% 0.21/0.49    inference(resolution,[],[f42,f69])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f34,f37])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k9_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(k1_mcart_1(X4))) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f304,plain,(
% 0.21/0.49    spl9_20 | spl9_21 | spl9_22 | spl9_23 | spl9_24 | ~spl9_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f300,f67,f171,f167,f163,f159,f155])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    spl9_24 <=> k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.21/0.49  fof(f300,plain,(
% 0.21/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(sK8) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl9_6),
% 0.21/0.49    inference(resolution,[],[f69,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f36,f37])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k11_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(X4) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f303,plain,(
% 0.21/0.49    spl9_20 | spl9_21 | spl9_22 | spl9_23 | spl9_25 | ~spl9_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f299,f67,f177,f167,f163,f159,f155])).
% 0.21/0.49  fof(f177,plain,(
% 0.21/0.49    spl9_25 <=> k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_25])])).
% 0.21/0.49  fof(f299,plain,(
% 0.21/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) = k2_mcart_1(k1_mcart_1(sK8)) | k1_xboole_0 = sK3 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | ~spl9_6),
% 0.21/0.49    inference(resolution,[],[f69,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2),X3)) | k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(definition_unfolding,[],[f35,f37])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (k10_mcart_1(X0,X1,X2,X3,X4) = k2_mcart_1(k1_mcart_1(X4)) | ~m1_subset_1(X4,k4_zfmisc_1(X0,X1,X2,X3)) | k1_xboole_0 = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f296,plain,(
% 0.21/0.49    ~spl9_41 | ~spl9_9 | ~spl9_39),
% 0.21/0.49    inference(avatar_split_clause,[],[f291,f277,f82,f293])).
% 0.21/0.49  fof(f293,plain,(
% 0.21/0.49    spl9_41 <=> v1_xboole_0(sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl9_9 <=> m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    spl9_39 <=> r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.21/0.49  fof(f291,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1) | (~spl9_9 | ~spl9_39)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f84,f279,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~spl9_39),
% 0.21/0.49    inference(avatar_component_clause,[],[f277])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    m1_subset_1(sK5,k1_zfmisc_1(sK1)) | ~spl9_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f82])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    ~spl9_40 | ~spl9_10 | ~spl9_38),
% 0.21/0.49    inference(avatar_split_clause,[],[f284,f272,f87,f286])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    spl9_40 <=> v1_xboole_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl9_10 <=> m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    spl9_38 <=> r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    ~v1_xboole_0(sK0) | (~spl9_10 | ~spl9_38)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f89,f274,f31])).
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | ~spl9_38),
% 0.21/0.49    inference(avatar_component_clause,[],[f272])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    m1_subset_1(sK4,k1_zfmisc_1(sK0)) | ~spl9_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    spl9_38 | ~spl9_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f265,f107,f272])).
% 0.21/0.49  fof(f107,plain,(
% 0.21/0.49    spl9_13 <=> r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK4) | ~spl9_13),
% 0.21/0.49    inference(resolution,[],[f109,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k1_mcart_1(X0),X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) | ~spl9_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f107])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    spl9_39 | ~spl9_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f264,f107,f277])).
% 0.21/0.49  fof(f264,plain,(
% 0.21/0.49    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1(sK8))),sK5) | ~spl9_13),
% 0.21/0.49    inference(resolution,[],[f109,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | r2_hidden(k2_mcart_1(X0),X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    k10_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(k1_mcart_1(sK8)) | r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    k11_mcart_1(sK0,sK1,sK2,sK3,sK8) != k2_mcart_1(sK8) | r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k2_mcart_1(sK8),sK7)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    k1_xboole_0 != sK3 | v1_xboole_0(sK3) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f245,plain,(
% 0.21/0.49    ~spl9_11 | ~spl9_12 | ~spl9_34),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f244])).
% 0.21/0.49  fof(f244,plain,(
% 0.21/0.49    $false | (~spl9_11 | ~spl9_12 | ~spl9_34)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f101,f235,f30])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,sK6)) ) | (~spl9_11 | ~spl9_34)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f94,f233,f31])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) | ~spl9_34),
% 0.21/0.49    inference(avatar_component_clause,[],[f231])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    spl9_34 <=> m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    v1_xboole_0(k1_xboole_0) | ~spl9_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f92])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    spl9_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl9_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    spl9_12 <=> r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    spl9_34 | ~spl9_8 | ~spl9_22),
% 0.21/0.49    inference(avatar_split_clause,[],[f224,f163,f77,f231])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    spl9_8 <=> m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) | (~spl9_8 | ~spl9_22)),
% 0.21/0.49    inference(backward_demodulation,[],[f79,f165])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl9_22),
% 0.21/0.49    inference(avatar_component_clause,[],[f163])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    m1_subset_1(sK6,k1_zfmisc_1(sK2)) | ~spl9_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f77])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~spl9_16 | ~spl9_7 | ~spl9_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f131,f122,f72,f134])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    spl9_16 <=> v1_xboole_0(sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl9_7 <=> m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.49  fof(f122,plain,(
% 0.21/0.49    spl9_15 <=> r2_hidden(k2_mcart_1(sK8),sK7)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~v1_xboole_0(sK3) | (~spl9_7 | ~spl9_15)),
% 0.21/0.49    inference(unit_resulting_resolution,[],[f124,f74,f31])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    m1_subset_1(sK7,k1_zfmisc_1(sK3)) | ~spl9_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f72])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    r2_hidden(k2_mcart_1(sK8),sK7) | ~spl9_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f122])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    spl9_14 | ~spl9_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f115,f99,f117])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl9_14 <=> r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    r2_hidden(k2_mcart_1(k1_mcart_1(sK8)),sK6) | ~spl9_12),
% 0.21/0.49    inference(resolution,[],[f30,f101])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    spl9_15 | ~spl9_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f114,f62,f122])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl9_5 <=> r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    r2_hidden(k2_mcart_1(sK8),sK7) | ~spl9_5),
% 0.21/0.49    inference(resolution,[],[f30,f64])).
% 0.21/0.50  % (3766)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7)) | ~spl9_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f62])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl9_13 | ~spl9_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f105,f99,f107])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    r2_hidden(k1_mcart_1(k1_mcart_1(sK8)),k2_zfmisc_1(sK4,sK5)) | ~spl9_12),
% 0.21/0.50    inference(resolution,[],[f101,f29])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl9_12 | ~spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f97,f62,f99])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    r2_hidden(k1_mcart_1(sK8),k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6)) | ~spl9_5),
% 0.21/0.50    inference(resolution,[],[f29,f64])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl9_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f92])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    v1_xboole_0(k1_xboole_0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl9_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f87])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    (((((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f10,f18,f17,f16,f15,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0))) => (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) & m1_subset_1(sK4,k1_zfmisc_1(sK0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),X5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(X5,k1_zfmisc_1(sK1))) => (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) & m1_subset_1(sK5,k1_zfmisc_1(sK1)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),X6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(X6,k1_zfmisc_1(sK2))) => (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) & m1_subset_1(sK6,k1_zfmisc_1(sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),X7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,X7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(X7,k1_zfmisc_1(sK3))) => (? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) & m1_subset_1(sK7,k1_zfmisc_1(sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X8] : ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,X8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,X8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,X8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,X8),sK4)) & r2_hidden(X8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(X8,k4_zfmisc_1(sK0,sK1,sK2,sK3))) => ((~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)) & r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7)) & m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : ((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3,X4] : (? [X5] : (? [X6] : (? [X7] : (? [X8] : (((~r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) | ~r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) | ~r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) | ~r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4)) & r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7))) & m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3))) & m1_subset_1(X7,k1_zfmisc_1(X3))) & m1_subset_1(X6,k1_zfmisc_1(X2))) & m1_subset_1(X5,k1_zfmisc_1(X1))) & m1_subset_1(X4,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.21/0.50    inference(negated_conjecture,[],[f7])).
% 0.21/0.50  % (3773)Refutation not found, incomplete strategy% (3773)------------------------------
% 0.21/0.50  % (3773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  fof(f7,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k1_zfmisc_1(X0)) => ! [X5] : (m1_subset_1(X5,k1_zfmisc_1(X1)) => ! [X6] : (m1_subset_1(X6,k1_zfmisc_1(X2)) => ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X3)) => ! [X8] : (m1_subset_1(X8,k4_zfmisc_1(X0,X1,X2,X3)) => (r2_hidden(X8,k4_zfmisc_1(X4,X5,X6,X7)) => (r2_hidden(k11_mcart_1(X0,X1,X2,X3,X8),X7) & r2_hidden(k10_mcart_1(X0,X1,X2,X3,X8),X6) & r2_hidden(k9_mcart_1(X0,X1,X2,X3,X8),X5) & r2_hidden(k8_mcart_1(X0,X1,X2,X3,X8),X4))))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl9_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f82])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    m1_subset_1(sK5,k1_zfmisc_1(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl9_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f77])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    m1_subset_1(sK6,k1_zfmisc_1(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl9_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f72])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    m1_subset_1(sK7,k1_zfmisc_1(sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl9_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f39,f67])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    m1_subset_1(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),sK2),sK3))),
% 0.21/0.50    inference(definition_unfolding,[],[f24,f37])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK8,k4_zfmisc_1(sK0,sK1,sK2,sK3))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    spl9_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f38,f62])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    r2_hidden(sK8,k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK4,sK5),sK6),sK7))),
% 0.21/0.50    inference(definition_unfolding,[],[f25,f37])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    r2_hidden(sK8,k4_zfmisc_1(sK4,sK5,sK6,sK7))),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ~spl9_1 | ~spl9_2 | ~spl9_3 | ~spl9_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f57,f53,f49,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl9_1 <=> r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl9_2 <=> r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl9_3 <=> r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    spl9_4 <=> r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~r2_hidden(k11_mcart_1(sK0,sK1,sK2,sK3,sK8),sK7) | ~r2_hidden(k10_mcart_1(sK0,sK1,sK2,sK3,sK8),sK6) | ~r2_hidden(k9_mcart_1(sK0,sK1,sK2,sK3,sK8),sK5) | ~r2_hidden(k8_mcart_1(sK0,sK1,sK2,sK3,sK8),sK4)),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (3768)------------------------------
% 0.21/0.50  % (3768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3768)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (3768)Memory used [KB]: 6524
% 0.21/0.50  % (3768)Time elapsed: 0.069 s
% 0.21/0.50  % (3768)------------------------------
% 0.21/0.50  % (3768)------------------------------
% 0.21/0.50  % (3762)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (3757)Success in time 0.132 s
%------------------------------------------------------------------------------
