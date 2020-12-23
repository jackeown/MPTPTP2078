%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relset_1__t47_relset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:10 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 149 expanded)
%              Number of leaves         :   22 (  64 expanded)
%              Depth                    :    7
%              Number of atoms          :  236 ( 381 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3758,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f119,f128,f139,f146,f170,f176,f250,f259,f343,f372,f1336,f3069,f3725,f3757])).

fof(f3757,plain,
    ( spl10_53
    | ~ spl10_580 ),
    inference(avatar_contradiction_clause,[],[f3756])).

fof(f3756,plain,
    ( $false
    | ~ spl10_53
    | ~ spl10_580 ),
    inference(subsumption_resolution,[],[f3742,f249])).

fof(f249,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ spl10_53 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl10_53
  <=> ~ m1_subset_1(sK7(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f3742,plain,
    ( m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ spl10_580 ),
    inference(resolution,[],[f3724,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',t1_subset)).

fof(f3724,plain,
    ( r2_hidden(sK7(sK2,sK3),sK1)
    | ~ spl10_580 ),
    inference(avatar_component_clause,[],[f3723])).

fof(f3723,plain,
    ( spl10_580
  <=> r2_hidden(sK7(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_580])])).

fof(f3725,plain,
    ( spl10_580
    | ~ spl10_508 ),
    inference(avatar_split_clause,[],[f3696,f3067,f3723])).

fof(f3067,plain,
    ( spl10_508
  <=> r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_508])])).

fof(f3696,plain,
    ( r2_hidden(sK7(sK2,sK3),sK1)
    | ~ spl10_508 ),
    inference(resolution,[],[f3068,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',t106_zfmisc_1)).

fof(f3068,plain,
    ( r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_508 ),
    inference(avatar_component_clause,[],[f3067])).

fof(f3069,plain,
    ( spl10_508
    | spl10_67
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f1377,f1334,f370,f3067])).

fof(f370,plain,
    ( spl10_67
  <=> ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_67])])).

fof(f1334,plain,
    ( spl10_228
  <=> m1_subset_1(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_228])])).

fof(f1377,plain,
    ( r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_67
    | ~ spl10_228 ),
    inference(subsumption_resolution,[],[f1376,f371])).

fof(f371,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_67 ),
    inference(avatar_component_clause,[],[f370])).

fof(f1376,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_228 ),
    inference(resolution,[],[f1335,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',t2_subset)).

fof(f1335,plain,
    ( m1_subset_1(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_228 ),
    inference(avatar_component_clause,[],[f1334])).

fof(f1336,plain,
    ( spl10_228
    | ~ spl10_8
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f772,f174,f90,f1334])).

fof(f90,plain,
    ( spl10_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f174,plain,
    ( spl10_36
  <=> r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f772,plain,
    ( m1_subset_1(k4_tarski(sK3,sK7(sK2,sK3)),k2_zfmisc_1(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_36 ),
    inference(resolution,[],[f398,f91])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f398,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X3))
        | m1_subset_1(k4_tarski(sK3,sK7(sK2,sK3)),X3) )
    | ~ spl10_36 ),
    inference(resolution,[],[f175,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',t4_subset)).

fof(f175,plain,
    ( r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),sK2)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f174])).

fof(f372,plain,
    ( ~ spl10_67
    | ~ spl10_8
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f337,f174,f90,f370])).

fof(f337,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl10_8
    | ~ spl10_36 ),
    inference(resolution,[],[f205,f91])).

fof(f205,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl10_36 ),
    inference(resolution,[],[f175,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',t5_subset)).

fof(f343,plain,
    ( spl10_22
    | ~ spl10_16 ),
    inference(avatar_split_clause,[],[f280,f117,f137])).

fof(f137,plain,
    ( spl10_22
  <=> sP6(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f117,plain,
    ( spl10_16
  <=> r2_hidden(k4_tarski(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f280,plain,
    ( sP6(sK3,sK2)
    | ~ spl10_16 ),
    inference(resolution,[],[f118,f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',d4_relat_1)).

fof(f118,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f117])).

fof(f259,plain,
    ( spl10_13
    | ~ spl10_22
    | ~ spl10_34 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl10_13
    | ~ spl10_22
    | ~ spl10_34 ),
    inference(subsumption_resolution,[],[f152,f255])).

fof(f255,plain,
    ( ~ r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl10_13
    | ~ spl10_34 ),
    inference(forward_demodulation,[],[f142,f169])).

fof(f169,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl10_34
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f142,plain,
    ( ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl10_13
  <=> ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f152,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl10_22 ),
    inference(resolution,[],[f138,f70])).

fof(f70,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f138,plain,
    ( sP6(sK3,sK2)
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f137])).

fof(f250,plain,
    ( ~ spl10_53
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f202,f174,f144,f248])).

fof(f144,plain,
    ( spl10_24
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | ~ r2_hidden(k4_tarski(sK3,X4),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f202,plain,
    ( ~ m1_subset_1(sK7(sK2,sK3),sK1)
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(resolution,[],[f175,f145])).

fof(f145,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k4_tarski(sK3,X4),sK2)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f144])).

fof(f176,plain,
    ( spl10_36
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f151,f137,f174])).

fof(f151,plain,
    ( r2_hidden(k4_tarski(sK3,sK7(sK2,sK3)),sK2)
    | ~ spl10_22 ),
    inference(resolution,[],[f138,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ sP6(X2,X0)
      | r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f170,plain,
    ( spl10_34
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f99,f90,f168])).

fof(f99,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl10_8 ),
    inference(resolution,[],[f91,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',redefinition_k1_relset_1)).

fof(f146,plain,
    ( ~ spl10_13
    | spl10_24 ),
    inference(avatar_split_clause,[],[f42,f144,f141])).

fof(f42,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | ~ r2_hidden(k4_tarski(sK3,X4),sK2)
      | ~ r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <~> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                    <=> ? [X4] :
                          ( r2_hidden(k4_tarski(X3,X4),X2)
                          & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,k1_relset_1(X0,X1,X2))
                  <=> ? [X4] :
                        ( r2_hidden(k4_tarski(X3,X4),X2)
                        & m1_subset_1(X4,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relset_1__t47_relset_1.p',t47_relset_1)).

fof(f139,plain,
    ( spl10_22
    | ~ spl10_20 ),
    inference(avatar_split_clause,[],[f129,f126,f137])).

fof(f126,plain,
    ( spl10_20
  <=> r2_hidden(sK3,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f129,plain,
    ( sP6(sK3,sK2)
    | ~ spl10_20 ),
    inference(resolution,[],[f127,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f127,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( spl10_20
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f120,f108,f90,f126])).

fof(f108,plain,
    ( spl10_12
  <=> r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f120,plain,
    ( r2_hidden(sK3,k1_relat_1(sK2))
    | ~ spl10_8
    | ~ spl10_12 ),
    inference(forward_demodulation,[],[f109,f99])).

fof(f109,plain,
    ( r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f119,plain,
    ( spl10_12
    | spl10_16 ),
    inference(avatar_split_clause,[],[f44,f117,f108])).

fof(f44,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),sK2)
    | r2_hidden(sK3,k1_relset_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f46,f90])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
