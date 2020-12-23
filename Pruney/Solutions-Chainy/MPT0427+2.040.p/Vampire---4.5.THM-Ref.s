%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 265 expanded)
%              Number of leaves         :   37 ( 115 expanded)
%              Depth                    :    9
%              Number of atoms          :  428 ( 732 expanded)
%              Number of equality atoms :   71 ( 135 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f264,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f69,f77,f81,f89,f94,f101,f111,f115,f119,f123,f137,f141,f150,f163,f173,f183,f214,f226,f231,f240,f246,f263])).

fof(f263,plain,
    ( ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_33
    | spl3_34 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_31
    | ~ spl3_33
    | spl3_34 ),
    inference(subsumption_resolution,[],[f261,f230])).

fof(f230,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f229])).

fof(f229,plain,
    ( spl3_31
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f261,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_16
    | ~ spl3_33
    | spl3_34 ),
    inference(forward_demodulation,[],[f260,f255])).

fof(f255,plain,
    ( sK0 = k1_setfam_1(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_7
    | ~ spl3_16
    | ~ spl3_33
    | spl3_34 ),
    inference(forward_demodulation,[],[f252,f68])).

fof(f68,plain,
    ( ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl3_7
  <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f252,plain,
    ( k1_setfam_1(k1_xboole_0) = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_16
    | ~ spl3_33
    | spl3_34 ),
    inference(backward_demodulation,[],[f239,f249])).

fof(f249,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_1
    | ~ spl3_16
    | spl3_34 ),
    inference(subsumption_resolution,[],[f247,f44])).

fof(f44,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl3_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f247,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_16
    | spl3_34 ),
    inference(resolution,[],[f245,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = X0
        | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f245,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f244])).

fof(f244,plain,
    ( spl3_34
  <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f239,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl3_33
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f260,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k1_setfam_1(k1_xboole_0)))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_16
    | spl3_34 ),
    inference(forward_demodulation,[],[f248,f249])).

fof(f248,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k1_setfam_1(sK1)))
    | ~ spl3_9
    | spl3_34 ),
    inference(resolution,[],[f245,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f246,plain,
    ( ~ spl3_34
    | spl3_30
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f242,f238,f224,f244])).

fof(f224,plain,
    ( spl3_30
  <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f242,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | spl3_30
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f225,f239])).

fof(f225,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f224])).

fof(f240,plain,
    ( spl3_33
    | spl3_28
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f152,f148,f51,f197,f238])).

fof(f197,plain,
    ( spl3_28
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f51,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f148,plain,
    ( spl3_23
  <=> ! [X3,X2] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f152,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(resolution,[],[f149,f52])).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f149,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | k1_xboole_0 = X3
        | k1_setfam_1(X3) = k8_setfam_1(X2,X3) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f148])).

fof(f231,plain,
    ( spl3_31
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f209,f158,f121,f47,f229])).

fof(f47,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f121,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f158,plain,
    ( spl3_24
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f209,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(subsumption_resolution,[],[f205,f48])).

fof(f48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f205,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_19
    | ~ spl3_24 ),
    inference(superposition,[],[f122,f159])).

fof(f159,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f158])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f121])).

fof(f226,plain,
    ( ~ spl3_30
    | spl3_4
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f220,f158,f55,f224])).

fof(f55,plain,
    ( spl3_4
  <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f220,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | spl3_4
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f56,f159])).

fof(f56,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f214,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | spl3_13
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_7
    | spl3_13
    | ~ spl3_19
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f212,f209])).

fof(f212,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_7
    | spl3_13
    | ~ spl3_24
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f211,f159])).

fof(f211,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_7
    | spl3_13
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f210,f68])).

fof(f210,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | spl3_13
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f93,f198])).

fof(f198,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f197])).

fof(f93,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_13
  <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f183,plain,
    ( ~ spl3_7
    | spl3_13
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl3_7
    | spl3_13
    | ~ spl3_18
    | ~ spl3_22
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f181,f140])).

fof(f140,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_22
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f181,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl3_7
    | spl3_13
    | ~ spl3_18
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f177,f68])).

fof(f177,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0)))
    | ~ spl3_7
    | spl3_13
    | ~ spl3_18
    | ~ spl3_25
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f168,f174])).

fof(f174,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_18
    | ~ spl3_26 ),
    inference(resolution,[],[f172,f118])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_18
  <=> ! [X1] :
        ( k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f172,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_26
  <=> r1_tarski(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f168,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | ~ spl3_7
    | spl3_13
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f164,f68])).

fof(f164,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_13
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f93,f162])).

fof(f162,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl3_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f173,plain,
    ( spl3_26
    | ~ spl3_1
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f167,f161,f43,f171])).

fof(f167,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_25 ),
    inference(backward_demodulation,[],[f44,f162])).

fof(f163,plain,
    ( spl3_24
    | spl3_25
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f151,f148,f47,f161,f158])).

fof(f151,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_2
    | ~ spl3_23 ),
    inference(resolution,[],[f149,f48])).

fof(f150,plain,
    ( spl3_23
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f145,f135,f113,f148])).

fof(f113,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f135,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k1_xboole_0 = X1
        | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f145,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(duplicate_literal_removal,[],[f142])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
        | k1_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) )
    | ~ spl3_17
    | ~ spl3_21 ),
    inference(superposition,[],[f136,f114])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f113])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f135])).

fof(f141,plain,
    ( spl3_22
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f133,f121,f67,f63,f139])).

fof(f63,plain,
    ( spl3_6
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f133,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f132,f64])).

fof(f64,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f132,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl3_7
    | ~ spl3_19 ),
    inference(superposition,[],[f122,f68])).

fof(f137,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f34,f135])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f123,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f32,f121])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f119,plain,
    ( spl3_18
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f106,f99,f79,f117])).

fof(f79,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f99,plain,
    ( spl3_14
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f106,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(superposition,[],[f100,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f100,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f99])).

fof(f115,plain,(
    spl3_17 ),
    inference(avatar_split_clause,[],[f31,f113])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f111,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f30,f109])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f101,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f96,f87,f59,f99])).

fof(f59,plain,
    ( spl3_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f87,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f96,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f94,plain,
    ( ~ spl3_13
    | spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f90,f75,f55,f92])).

fof(f90,plain,
    ( ~ m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))
    | spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f76,f56])).

fof(f89,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f36,f87])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f81,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f79])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f77,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f38,f75])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f69,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f41,f67])).

fof(f41,plain,(
    ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f40,f28])).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 != X1
      | k8_setfam_1(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f65,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f28,f63])).

fof(f61,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f57,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f25,f55])).

fof(f25,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f53,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f51])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f47])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f24,f43])).

fof(f24,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:14:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (2619)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.42  % (2619)Refutation not found, incomplete strategy% (2619)------------------------------
% 0.22/0.42  % (2619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (2619)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.42  
% 0.22/0.42  % (2619)Memory used [KB]: 1663
% 0.22/0.42  % (2619)Time elapsed: 0.004 s
% 0.22/0.42  % (2619)------------------------------
% 0.22/0.42  % (2619)------------------------------
% 0.22/0.46  % (2621)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.46  % (2621)Refutation not found, incomplete strategy% (2621)------------------------------
% 0.22/0.46  % (2621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (2621)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (2621)Memory used [KB]: 6140
% 0.22/0.46  % (2621)Time elapsed: 0.046 s
% 0.22/0.46  % (2621)------------------------------
% 0.22/0.46  % (2621)------------------------------
% 0.22/0.48  % (2613)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.48  % (2620)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (2622)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (2612)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (2610)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (2615)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (2606)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (2609)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (2615)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f264,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f45,f49,f53,f57,f61,f65,f69,f77,f81,f89,f94,f101,f111,f115,f119,f123,f137,f141,f150,f163,f173,f183,f214,f226,f231,f240,f246,f263])).
% 0.22/0.50  fof(f263,plain,(
% 0.22/0.50    ~spl3_1 | ~spl3_7 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_33 | spl3_34),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f262])).
% 0.22/0.50  fof(f262,plain,(
% 0.22/0.50    $false | (~spl3_1 | ~spl3_7 | ~spl3_9 | ~spl3_16 | ~spl3_31 | ~spl3_33 | spl3_34)),
% 0.22/0.50    inference(subsumption_resolution,[],[f261,f230])).
% 0.22/0.50  fof(f230,plain,(
% 0.22/0.50    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_31),
% 0.22/0.50    inference(avatar_component_clause,[],[f229])).
% 0.22/0.50  fof(f229,plain,(
% 0.22/0.50    spl3_31 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.50  fof(f261,plain,(
% 0.22/0.50    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_7 | ~spl3_9 | ~spl3_16 | ~spl3_33 | spl3_34)),
% 0.22/0.50    inference(forward_demodulation,[],[f260,f255])).
% 0.22/0.50  fof(f255,plain,(
% 0.22/0.50    sK0 = k1_setfam_1(k1_xboole_0) | (~spl3_1 | ~spl3_7 | ~spl3_16 | ~spl3_33 | spl3_34)),
% 0.22/0.50    inference(forward_demodulation,[],[f252,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) ) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl3_7 <=> ! [X0] : k8_setfam_1(X0,k1_xboole_0) = X0),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    k1_setfam_1(k1_xboole_0) = k8_setfam_1(sK0,k1_xboole_0) | (~spl3_1 | ~spl3_16 | ~spl3_33 | spl3_34)),
% 0.22/0.50    inference(backward_demodulation,[],[f239,f249])).
% 0.22/0.50  fof(f249,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | (~spl3_1 | ~spl3_16 | spl3_34)),
% 0.22/0.50    inference(subsumption_resolution,[],[f247,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2) | ~spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    spl3_1 <=> r1_tarski(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f247,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl3_16 | spl3_34)),
% 0.22/0.50    inference(resolution,[],[f245,f110])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl3_16 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.50  fof(f245,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | spl3_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f244])).
% 0.22/0.50  fof(f244,plain,(
% 0.22/0.50    spl3_34 <=> r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f238])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    spl3_33 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  fof(f260,plain,(
% 0.22/0.50    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k1_setfam_1(k1_xboole_0))) | (~spl3_1 | ~spl3_9 | ~spl3_16 | spl3_34)),
% 0.22/0.50    inference(forward_demodulation,[],[f248,f249])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(k1_setfam_1(sK1))) | (~spl3_9 | spl3_34)),
% 0.22/0.50    inference(resolution,[],[f245,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_9 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f246,plain,(
% 0.22/0.50    ~spl3_34 | spl3_30 | ~spl3_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f242,f238,f224,f244])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    spl3_30 <=> r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.50  fof(f242,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (spl3_30 | ~spl3_33)),
% 0.22/0.50    inference(backward_demodulation,[],[f225,f239])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | spl3_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f224])).
% 0.22/0.50  fof(f240,plain,(
% 0.22/0.50    spl3_33 | spl3_28 | ~spl3_3 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f152,f148,f51,f197,f238])).
% 0.22/0.50  fof(f197,plain,(
% 0.22/0.50    spl3_28 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl3_23 <=> ! [X3,X2] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | (~spl3_3 | ~spl3_23)),
% 0.22/0.50    inference(resolution,[],[f149,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f51])).
% 0.22/0.50  fof(f149,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) ) | ~spl3_23),
% 0.22/0.50    inference(avatar_component_clause,[],[f148])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    spl3_31 | ~spl3_2 | ~spl3_19 | ~spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f209,f158,f121,f47,f229])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl3_19 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    spl3_24 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | ~spl3_19 | ~spl3_24)),
% 0.22/0.50    inference(subsumption_resolution,[],[f205,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f47])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_19 | ~spl3_24)),
% 0.22/0.50    inference(superposition,[],[f122,f159])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f158])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f121])).
% 0.22/0.50  fof(f226,plain,(
% 0.22/0.50    ~spl3_30 | spl3_4 | ~spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f220,f158,f55,f224])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl3_4 <=> r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f220,plain,(
% 0.22/0.50    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | (spl3_4 | ~spl3_24)),
% 0.22/0.50    inference(forward_demodulation,[],[f56,f159])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) | spl3_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f214,plain,(
% 0.22/0.50    ~spl3_2 | ~spl3_7 | spl3_13 | ~spl3_19 | ~spl3_24 | ~spl3_28),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f213])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    $false | (~spl3_2 | ~spl3_7 | spl3_13 | ~spl3_19 | ~spl3_24 | ~spl3_28)),
% 0.22/0.50    inference(subsumption_resolution,[],[f212,f209])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | (~spl3_7 | spl3_13 | ~spl3_24 | ~spl3_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f211,f159])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_7 | spl3_13 | ~spl3_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f210,f68])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (spl3_13 | ~spl3_28)),
% 0.22/0.50    inference(forward_demodulation,[],[f93,f198])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~spl3_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f197])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | spl3_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f92])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    spl3_13 <=> m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.50  fof(f183,plain,(
% 0.22/0.50    ~spl3_7 | spl3_13 | ~spl3_18 | ~spl3_22 | ~spl3_25 | ~spl3_26),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f182])).
% 0.22/0.50  fof(f182,plain,(
% 0.22/0.50    $false | (~spl3_7 | spl3_13 | ~spl3_18 | ~spl3_22 | ~spl3_25 | ~spl3_26)),
% 0.22/0.50    inference(subsumption_resolution,[],[f181,f140])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl3_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f139])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl3_22 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | (~spl3_7 | spl3_13 | ~spl3_18 | ~spl3_25 | ~spl3_26)),
% 0.22/0.50    inference(forward_demodulation,[],[f177,f68])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,k1_xboole_0))) | (~spl3_7 | spl3_13 | ~spl3_18 | ~spl3_25 | ~spl3_26)),
% 0.22/0.50    inference(backward_demodulation,[],[f168,f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | (~spl3_18 | ~spl3_26)),
% 0.22/0.50    inference(resolution,[],[f172,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl3_18 <=> ! [X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k1_xboole_0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_xboole_0) | ~spl3_26),
% 0.22/0.50    inference(avatar_component_clause,[],[f171])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl3_26 <=> r1_tarski(sK1,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    ~m1_subset_1(sK0,k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | (~spl3_7 | spl3_13 | ~spl3_25)),
% 0.22/0.50    inference(forward_demodulation,[],[f164,f68])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    ~m1_subset_1(k8_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | (spl3_13 | ~spl3_25)),
% 0.22/0.50    inference(backward_demodulation,[],[f93,f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | ~spl3_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl3_25 <=> k1_xboole_0 = sK2),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.50  fof(f173,plain,(
% 0.22/0.50    spl3_26 | ~spl3_1 | ~spl3_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f167,f161,f43,f171])).
% 0.22/0.50  fof(f167,plain,(
% 0.22/0.50    r1_tarski(sK1,k1_xboole_0) | (~spl3_1 | ~spl3_25)),
% 0.22/0.50    inference(backward_demodulation,[],[f44,f162])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl3_24 | spl3_25 | ~spl3_2 | ~spl3_23),
% 0.22/0.50    inference(avatar_split_clause,[],[f151,f148,f47,f161,f158])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | (~spl3_2 | ~spl3_23)),
% 0.22/0.50    inference(resolution,[],[f149,f48])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl3_23 | ~spl3_17 | ~spl3_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f145,f135,f113,f148])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl3_17 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    spl3_21 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl3_17 | ~spl3_21)),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f142])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) ) | (~spl3_17 | ~spl3_21)),
% 0.22/0.50    inference(superposition,[],[f136,f114])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f113])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl3_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f135])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl3_22 | ~spl3_6 | ~spl3_7 | ~spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f133,f121,f67,f63,f139])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_6 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | (~spl3_6 | ~spl3_7 | ~spl3_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f132,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl3_7 | ~spl3_19)),
% 0.22/0.50    inference(superposition,[],[f122,f68])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl3_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f135])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    spl3_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f121])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl3_18 | ~spl3_10 | ~spl3_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f106,f99,f79,f117])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl3_10 <=> ! [X1,X0] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_14 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X1] : (k1_xboole_0 = X1 | ~r1_tarski(X1,k1_xboole_0)) ) | (~spl3_10 | ~spl3_14)),
% 0.22/0.50    inference(superposition,[],[f100,f80])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f79])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f99])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl3_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f113])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl3_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f109])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = X0 | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl3_14 | ~spl3_5 | ~spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f96,f87,f59,f99])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl3_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl3_12 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_5 | ~spl3_12)),
% 0.22/0.50    inference(resolution,[],[f88,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f87])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    ~spl3_13 | spl3_4 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f75,f55,f92])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    ~m1_subset_1(k8_setfam_1(sK0,sK2),k1_zfmisc_1(k8_setfam_1(sK0,sK1))) | (spl3_4 | ~spl3_9)),
% 0.22/0.50    inference(resolution,[],[f76,f56])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl3_12),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f87])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f79])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f75])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f41,f67])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(subsumption_resolution,[],[f40,f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(equality_resolution,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 != X1 | k8_setfam_1(X0,X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f63])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f59])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ~spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f25,f55])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f11])).
% 0.22/0.50  fof(f11,conjecture,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f51])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f47])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f24,f43])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    r1_tarski(sK1,sK2)),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (2615)------------------------------
% 0.22/0.50  % (2615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (2615)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (2615)Memory used [KB]: 10746
% 0.22/0.50  % (2615)Time elapsed: 0.085 s
% 0.22/0.50  % (2615)------------------------------
% 0.22/0.50  % (2615)------------------------------
% 0.22/0.50  % (2607)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (2624)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (2607)Refutation not found, incomplete strategy% (2607)------------------------------
% 0.22/0.51  % (2607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (2607)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (2607)Memory used [KB]: 10618
% 0.22/0.51  % (2607)Time elapsed: 0.090 s
% 0.22/0.51  % (2607)------------------------------
% 0.22/0.51  % (2607)------------------------------
% 0.22/0.51  % (2617)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.51  % (2608)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (2605)Success in time 0.147 s
%------------------------------------------------------------------------------
