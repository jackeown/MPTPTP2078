%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:55 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  335 ( 873 expanded)
%              Number of leaves         :   78 ( 349 expanded)
%              Depth                    :   11
%              Number of atoms          : 1305 (3572 expanded)
%              Number of equality atoms :   72 ( 200 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f806,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f151,f152,f161,f167,f174,f182,f187,f207,f216,f234,f239,f251,f252,f254,f308,f323,f332,f336,f340,f372,f375,f376,f382,f405,f414,f418,f428,f429,f430,f437,f469,f473,f477,f481,f485,f518,f526,f533,f538,f545,f549,f581,f593,f597,f639,f643,f647,f651,f672,f676,f681,f686,f743,f798,f803,f805])).

fof(f805,plain,(
    ~ spl8_58 ),
    inference(avatar_contradiction_clause,[],[f804])).

fof(f804,plain,
    ( $false
    | ~ spl8_58 ),
    inference(resolution,[],[f742,f222])).

fof(f222,plain,(
    ! [X0] : ~ v1_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f78,f217])).

fof(f217,plain,(
    ! [X3] : sK6(X3) = X3 ),
    inference(global_subsumption,[],[f78,f211])).

fof(f211,plain,(
    ! [X3] :
      ( sK6(X3) = X3
      | v1_subset_1(sK6(X3),X3) ) ),
    inference(resolution,[],[f75,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK6(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f78,plain,(
    ! [X0] : ~ v1_subset_1(sK6(X0),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f742,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_58 ),
    inference(avatar_component_clause,[],[f740])).

fof(f740,plain,
    ( spl8_58
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).

fof(f803,plain,
    ( ~ spl8_60
    | ~ spl8_20
    | spl8_57 ),
    inference(avatar_split_clause,[],[f738,f683,f213,f800])).

fof(f800,plain,
    ( spl8_60
  <=> m1_subset_1(sK2(sK1,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f213,plain,
    ( spl8_20
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f683,plain,
    ( spl8_57
  <=> m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f738,plain,
    ( ~ m1_subset_1(sK2(sK1,sK1,sK1),sK1)
    | ~ spl8_20
    | spl8_57 ),
    inference(backward_demodulation,[],[f685,f215])).

fof(f215,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f213])).

fof(f685,plain,
    ( ~ m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | spl8_57 ),
    inference(avatar_component_clause,[],[f683])).

fof(f798,plain,
    ( ~ spl8_59
    | ~ spl8_20
    | spl8_55 ),
    inference(avatar_split_clause,[],[f737,f669,f213,f795])).

fof(f795,plain,
    ( spl8_59
  <=> r2_hidden(sK2(sK1,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).

fof(f669,plain,
    ( spl8_55
  <=> r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f737,plain,
    ( ~ r2_hidden(sK2(sK1,sK1,sK1),sK1)
    | ~ spl8_20
    | spl8_55 ),
    inference(backward_demodulation,[],[f671,f215])).

fof(f671,plain,
    ( ~ r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | spl8_55 ),
    inference(avatar_component_clause,[],[f669])).

fof(f743,plain,
    ( spl8_58
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f688,f213,f144,f740])).

fof(f144,plain,
    ( spl8_11
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f688,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl8_11
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f145,f215])).

fof(f145,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f686,plain,
    ( ~ spl8_57
    | spl8_10
    | spl8_55 ),
    inference(avatar_split_clause,[],[f675,f669,f139,f683])).

fof(f139,plain,
    ( spl8_10
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f675,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | spl8_55 ),
    inference(resolution,[],[f671,f61])).

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f681,plain,
    ( spl8_20
    | spl8_56
    | ~ spl8_42
    | ~ spl8_7
    | spl8_55 ),
    inference(avatar_split_clause,[],[f674,f669,f124,f511,f678,f213])).

fof(f678,plain,
    ( spl8_56
  <=> r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).

fof(f511,plain,
    ( spl8_42
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f124,plain,
    ( spl8_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f674,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | spl8_55 ),
    inference(resolution,[],[f671,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK2(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f676,plain,
    ( spl8_20
    | ~ spl8_42
    | ~ spl8_7
    | ~ spl8_32
    | spl8_55 ),
    inference(avatar_split_clause,[],[f673,f669,f403,f124,f511,f213])).

fof(f403,plain,
    ( spl8_32
  <=> ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f673,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ spl8_32
    | spl8_55 ),
    inference(resolution,[],[f671,f463])).

fof(f463,plain,
    ( ! [X8,X9] :
        ( r2_hidden(sK2(u1_struct_0(sK0),X8,X9),sK1)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
        | X8 = X9 )
    | ~ spl8_32 ),
    inference(resolution,[],[f404,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f404,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f403])).

fof(f672,plain,
    ( ~ spl8_55
    | spl8_20
    | ~ spl8_42
    | ~ spl8_7
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f664,f637,f124,f511,f213,f669])).

fof(f637,plain,
    ( spl8_51
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0)
        | sK1 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f664,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0)
    | ~ r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl8_7
    | ~ spl8_51 ),
    inference(resolution,[],[f638,f197])).

fof(f197,plain,
    ( ! [X5] :
        ( r2_hidden(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f60,f126])).

fof(f126,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f638,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f637])).

fof(f651,plain,
    ( ~ spl8_42
    | spl8_54
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f632,f403,f124,f649,f511])).

fof(f649,plain,
    ( spl8_54
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),X3),X3)
        | v1_xboole_0(X3)
        | u1_struct_0(sK0) = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).

fof(f632,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X3
        | v1_xboole_0(X3)
        | ~ m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),X3),X3) )
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f630])).

fof(f630,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X3
        | v1_xboole_0(X3)
        | ~ m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),X3),X3)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(resolution,[],[f463,f422])).

fof(f422,plain,
    ( ! [X8,X9] :
        ( ~ r2_hidden(sK2(X8,u1_struct_0(sK0),X9),sK1)
        | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
        | u1_struct_0(sK0) = X9
        | v1_xboole_0(X9)
        | ~ m1_subset_1(sK2(X8,u1_struct_0(sK0),X9),X9)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X8)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f290,f197])).

fof(f290,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(sK2(X4,X5,X3),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X4))
      | X3 = X5
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK2(X4,X5,X3),X3) ) ),
    inference(resolution,[],[f58,f61])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f647,plain,
    ( spl8_53
    | ~ spl8_42
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f633,f403,f124,f511,f645])).

fof(f645,plain,
    ( spl8_53
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(u1_struct_0(sK0),X2,u1_struct_0(sK0)),X2)
        | u1_struct_0(sK0) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f633,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X2
        | ~ r2_hidden(sK2(u1_struct_0(sK0),X2,u1_struct_0(sK0)),X2) )
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f629])).

fof(f629,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(u1_struct_0(sK0),X2,u1_struct_0(sK0)),X2)
        | u1_struct_0(sK0) = X2
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(resolution,[],[f463,f291])).

fof(f291,plain,
    ( ! [X6,X7] :
        ( ~ r2_hidden(sK2(X6,X7,u1_struct_0(sK0)),sK1)
        | ~ m1_subset_1(X7,k1_zfmisc_1(X6))
        | ~ r2_hidden(sK2(X6,X7,u1_struct_0(sK0)),X7)
        | u1_struct_0(sK0) = X7
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X6)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f58,f197])).

fof(f643,plain,
    ( ~ spl8_7
    | spl8_52
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f634,f403,f641,f124])).

fof(f641,plain,
    ( spl8_52
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1,X1),X1)
        | v1_xboole_0(X1)
        | sK1 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f634,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X1
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1,X1),X1) )
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f628])).

fof(f628,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X1
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X1
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2(u1_struct_0(sK0),sK1,X1),X1) )
    | ~ spl8_32 ),
    inference(resolution,[],[f463,f290])).

fof(f639,plain,
    ( spl8_51
    | ~ spl8_7
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f635,f403,f124,f637])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0) )
    | ~ spl8_32 ),
    inference(duplicate_literal_removal,[],[f627])).

fof(f627,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0)
        | sK1 = X0 )
    | ~ spl8_32 ),
    inference(resolution,[],[f463,f58])).

fof(f597,plain,
    ( ~ spl8_1
    | spl8_50
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f586,f579,f595,f94])).

fof(f94,plain,
    ( spl8_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f595,plain,
    ( spl8_50
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0))
        | k1_yellow_0(sK0,X8) = k1_yellow_0(sK0,X7)
        | ~ r2_lattice3(sK0,X7,k1_yellow_0(sK0,X8))
        | ~ r1_yellow_0(sK0,X7)
        | ~ r1_yellow_0(sK0,X8)
        | ~ r2_lattice3(sK0,sK1,sK7(sK0,X7,k1_yellow_0(sK0,X8))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f579,plain,
    ( spl8_48
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_lattice3(sK0,X4,X3)
        | ~ r2_lattice3(sK0,sK1,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f586,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK7(sK0,X7,k1_yellow_0(sK0,X8)))
        | ~ r1_yellow_0(sK0,X8)
        | ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X7)
        | ~ r2_lattice3(sK0,X7,k1_yellow_0(sK0,X8))
        | k1_yellow_0(sK0,X8) = k1_yellow_0(sK0,X7) )
    | ~ spl8_48 ),
    inference(duplicate_literal_removal,[],[f585])).

fof(f585,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK7(sK0,X7,k1_yellow_0(sK0,X8)))
        | ~ m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X8)
        | ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X7)
        | ~ r2_lattice3(sK0,X7,k1_yellow_0(sK0,X8))
        | k1_yellow_0(sK0,X8) = k1_yellow_0(sK0,X7) )
    | ~ spl8_48 ),
    inference(resolution,[],[f580,f313])).

fof(f313,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X1,sK7(X0,X2,k1_yellow_0(X0,X1)))
      | ~ m1_subset_1(sK7(X0,X2,k1_yellow_0(X0,X1)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k1_yellow_0(X0,X1))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ),
    inference(global_subsumption,[],[f79,f312])).

fof(f312,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK7(X0,X2,k1_yellow_0(X0,X1)),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,sK7(X0,X2,k1_yellow_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k1_yellow_0(X0,X1))
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(sK7(X0,X2,k1_yellow_0(X0,X1)),u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,sK7(X0,X2,k1_yellow_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k1_yellow_0(X0,X1))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2) ) ),
    inference(resolution,[],[f92,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r1_orders_2(X0,k1_yellow_0(X0,X1),X3)
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f580,plain,
    ( ! [X4,X3] :
        ( r2_lattice3(sK0,X4,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,X3) )
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f579])).

fof(f593,plain,
    ( ~ spl8_1
    | spl8_49
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f587,f579,f591,f94])).

fof(f591,plain,
    ( spl8_49
  <=> ! [X5,X4,X6] :
        ( ~ m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,X6)
        | k1_yellow_0(sK0,X4) = X5
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ r1_yellow_0(sK0,X4)
        | ~ r2_lattice3(sK0,sK1,sK7(sK0,X4,X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f587,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK7(sK0,X4,X5))
        | ~ r1_yellow_0(sK0,X4)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,X4) = X5
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_48 ),
    inference(duplicate_literal_removal,[],[f584])).

fof(f584,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK1,sK7(sK0,X4,X5))
        | ~ r1_yellow_0(sK0,X4)
        | ~ r2_lattice3(sK0,X4,X5)
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,X4) = X5
        | ~ m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0))
        | ~ r2_hidden(X5,X6)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl8_48 ),
    inference(resolution,[],[f580,f303])).

fof(f303,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X1,X3,sK7(X1,X2,X0))
      | ~ r1_yellow_0(X1,X2)
      | ~ r2_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | k1_yellow_0(X1,X2) = X0
      | ~ m1_subset_1(sK7(X1,X2,X0),u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f302])).

fof(f302,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_yellow_0(X1,X2)
      | ~ r2_lattice3(X1,X2,X0)
      | ~ l1_orders_2(X1)
      | k1_yellow_0(X1,X2) = X0
      | ~ m1_subset_1(sK7(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ l1_orders_2(X1)
      | ~ r2_lattice3(X1,X3,sK7(X1,X2,X0)) ) ),
    inference(resolution,[],[f85,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | ~ l1_orders_2(X0)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f581,plain,
    ( ~ spl8_1
    | spl8_48
    | ~ spl8_38 ),
    inference(avatar_split_clause,[],[f576,f471,f579,f94])).

fof(f471,plain,
    ( spl8_38
  <=> ! [X3,X2] :
        ( r2_hidden(sK3(sK0,X2,X3),sK1)
        | r2_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).

fof(f576,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,sK1,X3)
        | r2_lattice3(sK0,X4,X3) )
    | ~ spl8_38 ),
    inference(duplicate_literal_removal,[],[f573])).

fof(f573,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,sK1,X3)
        | r2_lattice3(sK0,X4,X3)
        | r2_lattice3(sK0,X4,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_38 ),
    inference(resolution,[],[f443,f472])).

fof(f472,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(sK0,X2,X3),sK1)
        | r2_lattice3(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl8_38 ),
    inference(avatar_component_clause,[],[f471])).

fof(f443,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK3(X1,X2,X0),X3)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ r2_lattice3(X1,X3,X0)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f439])).

fof(f439,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(sK3(X1,X2,X0),X3)
      | ~ l1_orders_2(X1)
      | ~ r2_lattice3(X1,X3,X0)
      | r2_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(resolution,[],[f282,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f282,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(sK3(X1,X2,X0),X3)
      | ~ l1_orders_2(X1)
      | ~ r2_lattice3(X1,X3,X0)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(sK3(X1,X2,X0),u1_struct_0(X1))
      | ~ r2_hidden(sK3(X1,X2,X0),X3)
      | ~ l1_orders_2(X1)
      | ~ r2_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r2_lattice3(X1,X2,X0) ) ),
    inference(resolution,[],[f63,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f549,plain,
    ( spl8_10
    | spl8_47
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f540,f124,f547,f139])).

fof(f547,plain,
    ( spl8_47
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),X1)
        | v1_xboole_0(X1)
        | u1_struct_0(sK0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f540,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | u1_struct_0(sK0) = X1
        | v1_xboole_0(X1)
        | ~ m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),X1)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),sK1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f422,f61])).

fof(f545,plain,
    ( spl8_10
    | spl8_20
    | spl8_46
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f541,f124,f543,f213,f139])).

fof(f543,plain,
    ( spl8_46
  <=> ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | r2_hidden(sK2(X0,u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK2(X0,u1_struct_0(sK0),sK1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f541,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | sK1 = u1_struct_0(sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK2(X0,u1_struct_0(sK0),sK1),sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0))
        | r2_hidden(sK2(X0,u1_struct_0(sK0),sK1),u1_struct_0(sK0)) )
    | ~ spl8_7 ),
    inference(duplicate_literal_removal,[],[f539])).

fof(f539,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | sK1 = u1_struct_0(sK0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK2(X0,u1_struct_0(sK0),sK1),sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0))
        | r2_hidden(sK2(X0,u1_struct_0(sK0),sK1),u1_struct_0(sK0))
        | sK1 = u1_struct_0(sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f422,f57])).

fof(f538,plain,
    ( ~ spl8_1
    | spl8_45
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f534,f515,f536,f94])).

fof(f536,plain,
    ( spl8_45
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f515,plain,
    ( spl8_43
  <=> v13_waybel_0(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f534,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_43 ),
    inference(resolution,[],[f517,f316])).

fof(f316,plain,(
    ! [X6,X4,X5] :
      ( ~ v13_waybel_0(u1_struct_0(X4),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ r2_hidden(X5,u1_struct_0(X4))
      | ~ r1_orders_2(X4,X5,X6)
      | r2_hidden(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f71,f221])).

fof(f221,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f77,f217])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f517,plain,
    ( v13_waybel_0(u1_struct_0(sK0),sK0)
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f515])).

fof(f533,plain,
    ( spl8_10
    | spl8_44
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f528,f124,f531,f139])).

fof(f531,plain,
    ( spl8_44
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK2(X2,X1,u1_struct_0(sK0)),sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
        | u1_struct_0(sK0) = X1
        | ~ r2_hidden(sK2(X2,X1,u1_struct_0(sK0)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f528,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
        | ~ r2_hidden(sK2(X2,X1,u1_struct_0(sK0)),X1)
        | u1_struct_0(sK0) = X1
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2))
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK2(X2,X1,u1_struct_0(sK0)),sK1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f291,f61])).

fof(f526,plain,(
    spl8_42 ),
    inference(avatar_contradiction_clause,[],[f525])).

fof(f525,plain,
    ( $false
    | spl8_42 ),
    inference(resolution,[],[f513,f221])).

fof(f513,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_42 ),
    inference(avatar_component_clause,[],[f511])).

fof(f518,plain,
    ( ~ spl8_1
    | ~ spl8_42
    | spl8_43
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f509,f479,f124,f515,f511,f94])).

fof(f479,plain,
    ( spl8_40
  <=> ! [X5] :
        ( r2_hidden(sK5(sK0,X5),sK1)
        | v13_waybel_0(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f509,plain,
    ( v13_waybel_0(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(duplicate_literal_removal,[],[f505])).

fof(f505,plain,
    ( v13_waybel_0(u1_struct_0(sK0),sK0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | v13_waybel_0(u1_struct_0(sK0),sK0)
    | ~ spl8_7
    | ~ spl8_40 ),
    inference(resolution,[],[f480,f274])).

fof(f274,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1)
        | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_orders_2(X1)
        | v13_waybel_0(u1_struct_0(sK0),X1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f197,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f480,plain,
    ( ! [X5] :
        ( r2_hidden(sK5(sK0,X5),sK1)
        | v13_waybel_0(X5,sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f479])).

fof(f485,plain,
    ( ~ spl8_1
    | spl8_41
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f462,f403,f483,f94])).

fof(f483,plain,
    ( spl8_41
  <=> ! [X7,X6] :
        ( r2_hidden(sK7(sK0,X6,X7),sK1)
        | k1_yellow_0(sK0,X6) = X7
        | ~ r2_lattice3(sK0,X6,X7)
        | ~ r1_yellow_0(sK0,X6)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f462,plain,
    ( ! [X6,X7] :
        ( r2_hidden(sK7(sK0,X6,X7),sK1)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X6)
        | ~ r2_lattice3(sK0,X6,X7)
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,X6) = X7 )
    | ~ spl8_32 ),
    inference(resolution,[],[f404,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f481,plain,
    ( ~ spl8_1
    | spl8_40
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f461,f403,f479,f94])).

fof(f461,plain,
    ( ! [X5] :
        ( r2_hidden(sK5(sK0,X5),sK1)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v13_waybel_0(X5,sK0) )
    | ~ spl8_32 ),
    inference(resolution,[],[f404,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK5(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f477,plain,
    ( ~ spl8_1
    | spl8_39
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f460,f403,f475,f94])).

fof(f475,plain,
    ( spl8_39
  <=> ! [X4] :
        ( r2_hidden(sK4(sK0,X4),sK1)
        | v13_waybel_0(X4,sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f460,plain,
    ( ! [X4] :
        ( r2_hidden(sK4(sK0,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v13_waybel_0(X4,sK0) )
    | ~ spl8_32 ),
    inference(resolution,[],[f404,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f473,plain,
    ( ~ spl8_1
    | spl8_38
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f459,f403,f471,f94])).

fof(f459,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK3(sK0,X2,X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r2_lattice3(sK0,X2,X3) )
    | ~ spl8_32 ),
    inference(resolution,[],[f404,f64])).

fof(f469,plain,
    ( ~ spl8_1
    | spl8_37
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f458,f403,f467,f94])).

fof(f467,plain,
    ( spl8_37
  <=> ! [X1] : r2_hidden(k1_yellow_0(sK0,X1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f458,plain,
    ( ! [X1] :
        ( r2_hidden(k1_yellow_0(sK0,X1),sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_32 ),
    inference(resolution,[],[f404,f79])).

fof(f437,plain,
    ( spl8_36
    | ~ spl8_34 ),
    inference(avatar_split_clause,[],[f431,f411,f434])).

fof(f434,plain,
    ( spl8_36
  <=> m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f411,plain,
    ( spl8_34
  <=> r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f431,plain,
    ( m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ spl8_34 ),
    inference(resolution,[],[f413,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f413,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ spl8_34 ),
    inference(avatar_component_clause,[],[f411])).

fof(f430,plain,
    ( ~ spl8_1
    | ~ spl8_29
    | spl8_33 ),
    inference(avatar_split_clause,[],[f427,f407,f362,f94])).

fof(f362,plain,
    ( spl8_29
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f407,plain,
    ( spl8_33
  <=> m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f427,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | spl8_33 ),
    inference(superposition,[],[f409,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

fof(f409,plain,
    ( ~ m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl8_33 ),
    inference(avatar_component_clause,[],[f407])).

fof(f429,plain,
    ( ~ spl8_1
    | spl8_33 ),
    inference(avatar_split_clause,[],[f426,f407,f94])).

fof(f426,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_33 ),
    inference(resolution,[],[f409,f79])).

fof(f428,plain,
    ( ~ spl8_34
    | ~ spl8_7
    | spl8_33 ),
    inference(avatar_split_clause,[],[f425,f407,f124,f411])).

fof(f425,plain,
    ( ~ r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ spl8_7
    | spl8_33 ),
    inference(resolution,[],[f409,f193])).

fof(f193,plain,
    ( ! [X5] :
        ( m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f55,f126])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f418,plain,
    ( ~ spl8_1
    | ~ spl8_31
    | spl8_35
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f399,f366,f416,f369,f94])).

fof(f369,plain,
    ( spl8_31
  <=> r1_yellow_0(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f416,plain,
    ( spl8_35
  <=> ! [X1] :
        ( r2_hidden(sK7(sK0,k1_xboole_0,X1),sK1)
        | k1_yellow_0(sK0,k1_xboole_0) = X1
        | ~ r2_lattice3(sK0,k1_xboole_0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK7(sK0,k1_xboole_0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f366,plain,
    ( spl8_30
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f399,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK0,k1_xboole_0,X1),sK1)
        | ~ m1_subset_1(sK7(sK0,k1_xboole_0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ r2_lattice3(sK0,k1_xboole_0,X1)
        | ~ l1_orders_2(sK0)
        | k1_yellow_0(sK0,k1_xboole_0) = X1 )
    | ~ spl8_30 ),
    inference(resolution,[],[f367,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK7(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f367,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,k1_xboole_0,X2)
        | r2_hidden(X2,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f366])).

fof(f414,plain,
    ( ~ spl8_1
    | ~ spl8_31
    | ~ spl8_33
    | spl8_34
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f400,f366,f411,f407,f369,f94])).

fof(f400,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_30 ),
    inference(duplicate_literal_removal,[],[f398])).

fof(f398,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1)
    | ~ m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ spl8_30 ),
    inference(resolution,[],[f367,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,k1_yellow_0(X0,X1))
      | ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f405,plain,
    ( ~ spl8_1
    | spl8_32
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f401,f366,f403,f94])).

fof(f401,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0) )
    | ~ spl8_30 ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,
    ( ! [X0] :
        ( r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl8_30 ),
    inference(resolution,[],[f367,f265])).

fof(f265,plain,(
    ! [X4,X3] :
      ( r2_lattice3(X4,k1_xboole_0,X3)
      | ~ l1_orders_2(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f65,f190])).

fof(f190,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f154,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f154,plain,(
    ! [X2] : r1_tarski(k1_xboole_0,X2) ),
    inference(resolution,[],[f82,f80])).

fof(f80,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f382,plain,
    ( spl8_6
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3
    | spl8_31 ),
    inference(avatar_split_clause,[],[f381,f369,f104,f99,f94,f119])).

fof(f119,plain,
    ( spl8_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f99,plain,
    ( spl8_2
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f104,plain,
    ( spl8_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f381,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl8_31 ),
    inference(resolution,[],[f371,f88])).

fof(f88,plain,(
    ! [X0] :
      ( r1_yellow_0(X0,k1_xboole_0)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r2_yellow_0(X0,u1_struct_0(X0))
        & r1_yellow_0(X0,k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).

fof(f371,plain,
    ( ~ r1_yellow_0(sK0,k1_xboole_0)
    | spl8_31 ),
    inference(avatar_component_clause,[],[f369])).

fof(f376,plain,
    ( ~ spl8_1
    | spl8_29 ),
    inference(avatar_split_clause,[],[f374,f362,f94])).

fof(f374,plain,
    ( ~ l1_orders_2(sK0)
    | spl8_29 ),
    inference(resolution,[],[f364,f74])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f364,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f362])).

fof(f375,plain,
    ( ~ spl8_12
    | ~ spl8_7
    | spl8_29 ),
    inference(avatar_split_clause,[],[f373,f362,f124,f148])).

fof(f148,plain,
    ( spl8_12
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f373,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_7
    | spl8_29 ),
    inference(resolution,[],[f364,f193])).

fof(f372,plain,
    ( ~ spl8_12
    | ~ spl8_29
    | ~ spl8_1
    | spl8_30
    | ~ spl8_31
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f359,f321,f369,f366,f94,f362,f148])).

fof(f321,plain,
    ( spl8_25
  <=> ! [X11,X10] :
        ( ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r2_hidden(X11,sK1)
        | ~ r1_orders_2(sK0,X10,X11)
        | ~ r2_hidden(X10,sK1)
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f359,plain,
    ( ! [X2] :
        ( ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_xboole_0,X2)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X2,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1) )
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f358])).

fof(f358,plain,
    ( ! [X2] :
        ( ~ r1_yellow_0(sK0,k1_xboole_0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_xboole_0,X2)
        | ~ l1_orders_2(sK0)
        | r2_hidden(X2,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl8_25 ),
    inference(resolution,[],[f314,f322])).

fof(f322,plain,
    ( ! [X10,X11] :
        ( ~ r1_orders_2(sK0,X10,X11)
        | r2_hidden(X11,sK1)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_hidden(X10,sK1)
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) )
    | ~ spl8_25 ),
    inference(avatar_component_clause,[],[f321])).

fof(f314,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ r1_yellow_0(X0,k1_xboole_0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(global_subsumption,[],[f74,f311])).

fof(f311,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k1_xboole_0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f310])).

fof(f310,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k1_xboole_0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k1_xboole_0,X1)
      | ~ l1_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(superposition,[],[f92,f73])).

fof(f340,plain,
    ( ~ spl8_1
    | spl8_28
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f327,f321,f338,f94])).

fof(f338,plain,
    ( spl8_28
  <=> ! [X5,X4] :
        ( r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X5,X4)
        | ~ r1_yellow_0(sK0,X5)
        | ~ r2_hidden(k1_yellow_0(sK0,X5),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f327,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,sK1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0))
        | ~ r2_hidden(k1_yellow_0(sK0,X5),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X5)
        | ~ r2_lattice3(sK0,X5,X4)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f326])).

fof(f326,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,sK1)
        | ~ m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0))
        | ~ r2_hidden(k1_yellow_0(sK0,X5),sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X5)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X5,X4)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_25 ),
    inference(resolution,[],[f322,f92])).

fof(f336,plain,
    ( ~ spl8_1
    | spl8_27
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f328,f321,f334,f94])).

fof(f334,plain,
    ( spl8_27
  <=> ! [X1,X3,X2] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,X1)
        | ~ r2_hidden(X2,X3)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f328,plain,
    ( ! [X2,X3,X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,X3,X1) )
    | ~ spl8_25 ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( ! [X2,X3,X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ l1_orders_2(sK0)
        | ~ r2_lattice3(sK0,X3,X1) )
    | ~ spl8_25 ),
    inference(resolution,[],[f322,f63])).

fof(f332,plain,
    ( ~ spl8_1
    | spl8_26
    | ~ spl8_25 ),
    inference(avatar_split_clause,[],[f324,f321,f330,f94])).

fof(f330,plain,
    ( spl8_26
  <=> ! [X0] :
        ( r2_hidden(sK5(sK0,X0),sK1)
        | v13_waybel_0(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,X0),sK1)
        | ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f324,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),sK1)
        | ~ m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(sK0,X0),sK1)
        | ~ m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | v13_waybel_0(X0,sK0) )
    | ~ spl8_25 ),
    inference(resolution,[],[f322,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f323,plain,
    ( ~ spl8_8
    | spl8_25
    | ~ spl8_1
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f318,f124,f94,f321,f129])).

fof(f129,plain,
    ( spl8_8
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f318,plain,
    ( ! [X10,X11] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r2_hidden(X10,sK1)
        | ~ r1_orders_2(sK0,X10,X11)
        | r2_hidden(X11,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f71,f126])).

fof(f308,plain,
    ( spl8_10
    | spl8_24
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f304,f124,f306,f139])).

fof(f306,plain,
    ( spl8_24
  <=> ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(sK5(X0,u1_struct_0(sK0)),sK1)
        | v13_waybel_0(u1_struct_0(sK0),X0)
        | ~ l1_orders_2(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_orders_2(X0)
        | v13_waybel_0(u1_struct_0(sK0),X0)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(sK5(X0,u1_struct_0(sK0)),sK1) )
    | ~ spl8_7 ),
    inference(resolution,[],[f274,f61])).

fof(f254,plain,
    ( spl8_16
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f253,f148,f179])).

fof(f179,plain,
    ( spl8_16
  <=> m1_subset_1(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f253,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ spl8_12 ),
    inference(resolution,[],[f150,f62])).

fof(f150,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f252,plain,
    ( ~ spl8_1
    | spl8_16
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f247,f213,f179,f94])).

fof(f247,plain,
    ( m1_subset_1(k3_yellow_0(sK0),sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl8_20 ),
    inference(superposition,[],[f74,f215])).

fof(f251,plain,
    ( ~ spl8_1
    | spl8_23
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f246,f213,f249,f94])).

fof(f249,plain,
    ( spl8_23
  <=> ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f246,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_yellow_0(sK0,X0),sK1)
        | ~ l1_orders_2(sK0) )
    | ~ spl8_20 ),
    inference(superposition,[],[f79,f215])).

fof(f239,plain,
    ( ~ spl8_22
    | spl8_17
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f227,f213,f184,f236])).

fof(f236,plain,
    ( spl8_22
  <=> m1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f184,plain,
    ( spl8_17
  <=> m1_subset_1(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f227,plain,
    ( ~ m1_subset_1(sK1,sK1)
    | spl8_17
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f186,f215])).

fof(f186,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f234,plain,
    ( ~ spl8_21
    | spl8_14
    | ~ spl8_20 ),
    inference(avatar_split_clause,[],[f226,f213,f164,f231])).

fof(f231,plain,
    ( spl8_21
  <=> r2_hidden(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f164,plain,
    ( spl8_14
  <=> r2_hidden(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f226,plain,
    ( ~ r2_hidden(sK1,sK1)
    | spl8_14
    | ~ spl8_20 ),
    inference(backward_demodulation,[],[f166,f215])).

fof(f166,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | spl8_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f216,plain,
    ( spl8_11
    | spl8_20
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f210,f124,f213,f144])).

fof(f210,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl8_7 ),
    inference(resolution,[],[f75,f126])).

fof(f207,plain,
    ( spl8_18
    | spl8_19 ),
    inference(avatar_split_clause,[],[f199,f204,f201])).

fof(f201,plain,
    ( spl8_18
  <=> ! [X0] : ~ m1_subset_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f204,plain,
    ( spl8_19
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f199,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f190,f61])).

fof(f187,plain,
    ( ~ spl8_17
    | spl8_10
    | spl8_14 ),
    inference(avatar_split_clause,[],[f177,f164,f139,f184])).

fof(f177,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(u1_struct_0(sK0),sK1)
    | spl8_14 ),
    inference(resolution,[],[f61,f166])).

fof(f182,plain,
    ( ~ spl8_16
    | spl8_10
    | spl8_12 ),
    inference(avatar_split_clause,[],[f175,f148,f139,f179])).

fof(f175,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),sK1)
    | spl8_12 ),
    inference(resolution,[],[f61,f149])).

fof(f149,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f174,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f169,f171])).

fof(f171,plain,
    ( spl8_15
  <=> v1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f169,plain,(
    ~ v1_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f90,f80])).

fof(f90,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f167,plain,
    ( ~ spl8_14
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f162,f158,f164])).

fof(f158,plain,
    ( spl8_13
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f162,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),sK1)
    | ~ spl8_13 ),
    inference(resolution,[],[f160,f56])).

fof(f160,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl8_13
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f155,f124,f158])).

fof(f155,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl8_7 ),
    inference(resolution,[],[f82,f126])).

fof(f152,plain,
    ( spl8_11
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f43,f148,f144])).

fof(f43,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f151,plain,
    ( ~ spl8_11
    | spl8_12 ),
    inference(avatar_split_clause,[],[f44,f148,f144])).

fof(f44,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f142,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f45,f139])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f137,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f46,f134])).

fof(f134,plain,
    ( spl8_9
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f46,plain,(
    v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f132,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f47,f129])).

fof(f47,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f127,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f48,f124])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f122,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f49,f119])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f117,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f50,f114])).

fof(f114,plain,
    ( spl8_5
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f50,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f51,f109])).

fof(f109,plain,
    ( spl8_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f51,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f52,f104])).

fof(f52,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f53,f99])).

fof(f53,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f54,f94])).

fof(f54,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:22:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (32208)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.48  % (32224)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.48  % (32215)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.48  % (32220)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.49  % (32212)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.49  % (32216)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (32206)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (32219)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (32225)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (32217)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (32221)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (32211)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (32209)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (32228)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (32227)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (32213)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.52  % (32203)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.52  % (32205)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (32209)Refutation not found, incomplete strategy% (32209)------------------------------
% 0.20/0.54  % (32209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32209)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32209)Memory used [KB]: 10746
% 0.20/0.54  % (32209)Time elapsed: 0.080 s
% 0.20/0.54  % (32209)------------------------------
% 0.20/0.54  % (32209)------------------------------
% 0.20/0.54  % (32218)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (32214)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (32223)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.55  % (32204)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.55  % (32207)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.58/0.56  % (32210)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.58/0.56  % (32203)Refutation not found, incomplete strategy% (32203)------------------------------
% 1.58/0.56  % (32203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (32203)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (32203)Memory used [KB]: 10618
% 1.58/0.56  % (32203)Time elapsed: 0.133 s
% 1.58/0.56  % (32203)------------------------------
% 1.58/0.56  % (32203)------------------------------
% 1.58/0.56  % (32222)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.58/0.56  % (32210)Refutation not found, incomplete strategy% (32210)------------------------------
% 1.58/0.56  % (32210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (32210)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.56  
% 1.58/0.56  % (32210)Memory used [KB]: 1791
% 1.58/0.56  % (32210)Time elapsed: 0.159 s
% 1.58/0.56  % (32210)------------------------------
% 1.58/0.56  % (32210)------------------------------
% 1.58/0.56  % (32226)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.58/0.57  % (32212)Refutation not found, incomplete strategy% (32212)------------------------------
% 1.58/0.57  % (32212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (32212)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (32212)Memory used [KB]: 6268
% 1.58/0.57  % (32212)Time elapsed: 0.146 s
% 1.58/0.57  % (32212)------------------------------
% 1.58/0.57  % (32212)------------------------------
% 1.73/0.59  % (32220)Refutation found. Thanks to Tanya!
% 1.73/0.59  % SZS status Theorem for theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f806,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f117,f122,f127,f132,f137,f142,f151,f152,f161,f167,f174,f182,f187,f207,f216,f234,f239,f251,f252,f254,f308,f323,f332,f336,f340,f372,f375,f376,f382,f405,f414,f418,f428,f429,f430,f437,f469,f473,f477,f481,f485,f518,f526,f533,f538,f545,f549,f581,f593,f597,f639,f643,f647,f651,f672,f676,f681,f686,f743,f798,f803,f805])).
% 1.73/0.59  fof(f805,plain,(
% 1.73/0.59    ~spl8_58),
% 1.73/0.59    inference(avatar_contradiction_clause,[],[f804])).
% 1.73/0.59  fof(f804,plain,(
% 1.73/0.59    $false | ~spl8_58),
% 1.73/0.59    inference(resolution,[],[f742,f222])).
% 1.73/0.59  fof(f222,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_subset_1(X0,X0)) )),
% 1.73/0.59    inference(backward_demodulation,[],[f78,f217])).
% 1.73/0.59  fof(f217,plain,(
% 1.73/0.59    ( ! [X3] : (sK6(X3) = X3) )),
% 1.73/0.59    inference(global_subsumption,[],[f78,f211])).
% 1.73/0.59  fof(f211,plain,(
% 1.73/0.59    ( ! [X3] : (sK6(X3) = X3 | v1_subset_1(sK6(X3),X3)) )),
% 1.73/0.59    inference(resolution,[],[f75,f77])).
% 1.73/0.59  fof(f77,plain,(
% 1.73/0.59    ( ! [X0] : (m1_subset_1(sK6(X0),k1_zfmisc_1(X0))) )),
% 1.73/0.59    inference(cnf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 1.73/0.59  fof(f75,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f37])).
% 1.73/0.59  fof(f37,plain,(
% 1.73/0.59    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.59    inference(ennf_transformation,[],[f17])).
% 1.73/0.59  fof(f17,axiom,(
% 1.73/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.73/0.59  fof(f78,plain,(
% 1.73/0.59    ( ! [X0] : (~v1_subset_1(sK6(X0),X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f4])).
% 1.73/0.59  fof(f742,plain,(
% 1.73/0.59    v1_subset_1(sK1,sK1) | ~spl8_58),
% 1.73/0.59    inference(avatar_component_clause,[],[f740])).
% 1.73/0.59  fof(f740,plain,(
% 1.73/0.59    spl8_58 <=> v1_subset_1(sK1,sK1)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_58])])).
% 1.73/0.59  fof(f803,plain,(
% 1.73/0.59    ~spl8_60 | ~spl8_20 | spl8_57),
% 1.73/0.59    inference(avatar_split_clause,[],[f738,f683,f213,f800])).
% 1.73/0.59  fof(f800,plain,(
% 1.73/0.59    spl8_60 <=> m1_subset_1(sK2(sK1,sK1,sK1),sK1)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 1.73/0.59  fof(f213,plain,(
% 1.73/0.59    spl8_20 <=> sK1 = u1_struct_0(sK0)),
% 1.73/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 1.73/0.60  fof(f683,plain,(
% 1.73/0.60    spl8_57 <=> m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 1.73/0.60  fof(f738,plain,(
% 1.73/0.60    ~m1_subset_1(sK2(sK1,sK1,sK1),sK1) | (~spl8_20 | spl8_57)),
% 1.73/0.60    inference(backward_demodulation,[],[f685,f215])).
% 1.73/0.60  fof(f215,plain,(
% 1.73/0.60    sK1 = u1_struct_0(sK0) | ~spl8_20),
% 1.73/0.60    inference(avatar_component_clause,[],[f213])).
% 1.73/0.60  fof(f685,plain,(
% 1.73/0.60    ~m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | spl8_57),
% 1.73/0.60    inference(avatar_component_clause,[],[f683])).
% 1.73/0.60  fof(f798,plain,(
% 1.73/0.60    ~spl8_59 | ~spl8_20 | spl8_55),
% 1.73/0.60    inference(avatar_split_clause,[],[f737,f669,f213,f795])).
% 1.73/0.60  fof(f795,plain,(
% 1.73/0.60    spl8_59 <=> r2_hidden(sK2(sK1,sK1,sK1),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_59])])).
% 1.73/0.60  fof(f669,plain,(
% 1.73/0.60    spl8_55 <=> r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 1.73/0.60  fof(f737,plain,(
% 1.73/0.60    ~r2_hidden(sK2(sK1,sK1,sK1),sK1) | (~spl8_20 | spl8_55)),
% 1.73/0.60    inference(backward_demodulation,[],[f671,f215])).
% 1.73/0.60  fof(f671,plain,(
% 1.73/0.60    ~r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | spl8_55),
% 1.73/0.60    inference(avatar_component_clause,[],[f669])).
% 1.73/0.60  fof(f743,plain,(
% 1.73/0.60    spl8_58 | ~spl8_11 | ~spl8_20),
% 1.73/0.60    inference(avatar_split_clause,[],[f688,f213,f144,f740])).
% 1.73/0.60  fof(f144,plain,(
% 1.73/0.60    spl8_11 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 1.73/0.60  fof(f688,plain,(
% 1.73/0.60    v1_subset_1(sK1,sK1) | (~spl8_11 | ~spl8_20)),
% 1.73/0.60    inference(backward_demodulation,[],[f145,f215])).
% 1.73/0.60  fof(f145,plain,(
% 1.73/0.60    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_11),
% 1.73/0.60    inference(avatar_component_clause,[],[f144])).
% 1.73/0.60  fof(f686,plain,(
% 1.73/0.60    ~spl8_57 | spl8_10 | spl8_55),
% 1.73/0.60    inference(avatar_split_clause,[],[f675,f669,f139,f683])).
% 1.73/0.60  fof(f139,plain,(
% 1.73/0.60    spl8_10 <=> v1_xboole_0(sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.73/0.60  fof(f675,plain,(
% 1.73/0.60    v1_xboole_0(sK1) | ~m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | spl8_55),
% 1.73/0.60    inference(resolution,[],[f671,f61])).
% 1.73/0.60  fof(f61,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f29])).
% 1.73/0.60  fof(f29,plain,(
% 1.73/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.73/0.60    inference(flattening,[],[f28])).
% 1.73/0.60  fof(f28,plain,(
% 1.73/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.73/0.60    inference(ennf_transformation,[],[f6])).
% 1.73/0.60  fof(f6,axiom,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.73/0.60  fof(f681,plain,(
% 1.73/0.60    spl8_20 | spl8_56 | ~spl8_42 | ~spl8_7 | spl8_55),
% 1.73/0.60    inference(avatar_split_clause,[],[f674,f669,f124,f511,f678,f213])).
% 1.73/0.60  fof(f678,plain,(
% 1.73/0.60    spl8_56 <=> r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_56])])).
% 1.73/0.60  fof(f511,plain,(
% 1.73/0.60    spl8_42 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.73/0.60  fof(f124,plain,(
% 1.73/0.60    spl8_7 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.73/0.60  fof(f674,plain,(
% 1.73/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | spl8_55),
% 1.73/0.60    inference(resolution,[],[f671,f57])).
% 1.73/0.60  fof(f57,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,X1,X2),X1) | X1 = X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f26])).
% 1.73/0.60  fof(f26,plain,(
% 1.73/0.60    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.60    inference(flattening,[],[f25])).
% 1.73/0.60  fof(f25,plain,(
% 1.73/0.60    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f3])).
% 1.73/0.60  fof(f3,axiom,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 1.73/0.60  fof(f676,plain,(
% 1.73/0.60    spl8_20 | ~spl8_42 | ~spl8_7 | ~spl8_32 | spl8_55),
% 1.73/0.60    inference(avatar_split_clause,[],[f673,f669,f403,f124,f511,f213])).
% 1.73/0.60  fof(f403,plain,(
% 1.73/0.60    spl8_32 <=> ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.73/0.60  fof(f673,plain,(
% 1.73/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | (~spl8_32 | spl8_55)),
% 1.73/0.60    inference(resolution,[],[f671,f463])).
% 1.73/0.60  fof(f463,plain,(
% 1.73/0.60    ( ! [X8,X9] : (r2_hidden(sK2(u1_struct_0(sK0),X8,X9),sK1) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | X8 = X9) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f404,f59])).
% 1.73/0.60  fof(f59,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | X1 = X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f26])).
% 1.73/0.60  fof(f404,plain,(
% 1.73/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl8_32),
% 1.73/0.60    inference(avatar_component_clause,[],[f403])).
% 1.73/0.60  fof(f672,plain,(
% 1.73/0.60    ~spl8_55 | spl8_20 | ~spl8_42 | ~spl8_7 | ~spl8_51),
% 1.73/0.60    inference(avatar_split_clause,[],[f664,f637,f124,f511,f213,f669])).
% 1.73/0.60  fof(f637,plain,(
% 1.73/0.60    spl8_51 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0) | sK1 = X0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.73/0.60  fof(f664,plain,(
% 1.73/0.60    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0) | ~r2_hidden(sK2(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl8_7 | ~spl8_51)),
% 1.73/0.60    inference(resolution,[],[f638,f197])).
% 1.73/0.60  fof(f197,plain,(
% 1.73/0.60    ( ! [X5] : (r2_hidden(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f60,f126])).
% 1.73/0.60  fof(f126,plain,(
% 1.73/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl8_7),
% 1.73/0.60    inference(avatar_component_clause,[],[f124])).
% 1.73/0.60  fof(f60,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f27])).
% 1.73/0.60  fof(f27,plain,(
% 1.73/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f1])).
% 1.73/0.60  fof(f1,axiom,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.73/0.60  fof(f638,plain,(
% 1.73/0.60    ( ! [X0] : (~r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | ~spl8_51),
% 1.73/0.60    inference(avatar_component_clause,[],[f637])).
% 1.73/0.60  fof(f651,plain,(
% 1.73/0.60    ~spl8_42 | spl8_54 | ~spl8_7 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f632,f403,f124,f649,f511])).
% 1.73/0.60  fof(f649,plain,(
% 1.73/0.60    spl8_54 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),X3),X3) | v1_xboole_0(X3) | u1_struct_0(sK0) = X3)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_54])])).
% 1.73/0.60  fof(f632,plain,(
% 1.73/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X3 | v1_xboole_0(X3) | ~m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),X3),X3)) ) | (~spl8_7 | ~spl8_32)),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f630])).
% 1.73/0.60  fof(f630,plain,(
% 1.73/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X3 | v1_xboole_0(X3) | ~m1_subset_1(sK2(u1_struct_0(sK0),u1_struct_0(sK0),X3),X3) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl8_7 | ~spl8_32)),
% 1.73/0.60    inference(resolution,[],[f463,f422])).
% 1.73/0.60  fof(f422,plain,(
% 1.73/0.60    ( ! [X8,X9] : (~r2_hidden(sK2(X8,u1_struct_0(sK0),X9),sK1) | ~m1_subset_1(X9,k1_zfmisc_1(X8)) | u1_struct_0(sK0) = X9 | v1_xboole_0(X9) | ~m1_subset_1(sK2(X8,u1_struct_0(sK0),X9),X9) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X8))) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f290,f197])).
% 1.73/0.60  fof(f290,plain,(
% 1.73/0.60    ( ! [X4,X5,X3] : (~r2_hidden(sK2(X4,X5,X3),X5) | ~m1_subset_1(X5,k1_zfmisc_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X4)) | X3 = X5 | v1_xboole_0(X3) | ~m1_subset_1(sK2(X4,X5,X3),X3)) )),
% 1.73/0.60    inference(resolution,[],[f58,f61])).
% 1.73/0.60  fof(f58,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK2(X0,X1,X2),X1) | X1 = X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f26])).
% 1.73/0.60  fof(f647,plain,(
% 1.73/0.60    spl8_53 | ~spl8_42 | ~spl8_7 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f633,f403,f124,f511,f645])).
% 1.73/0.60  fof(f645,plain,(
% 1.73/0.60    spl8_53 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(u1_struct_0(sK0),X2,u1_struct_0(sK0)),X2) | u1_struct_0(sK0) = X2)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.73/0.60  fof(f633,plain,(
% 1.73/0.60    ( ! [X2] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X2 | ~r2_hidden(sK2(u1_struct_0(sK0),X2,u1_struct_0(sK0)),X2)) ) | (~spl8_7 | ~spl8_32)),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f629])).
% 1.73/0.60  fof(f629,plain,(
% 1.73/0.60    ( ! [X2] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(u1_struct_0(sK0),X2,u1_struct_0(sK0)),X2) | u1_struct_0(sK0) = X2 | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl8_7 | ~spl8_32)),
% 1.73/0.60    inference(resolution,[],[f463,f291])).
% 1.73/0.60  fof(f291,plain,(
% 1.73/0.60    ( ! [X6,X7] : (~r2_hidden(sK2(X6,X7,u1_struct_0(sK0)),sK1) | ~m1_subset_1(X7,k1_zfmisc_1(X6)) | ~r2_hidden(sK2(X6,X7,u1_struct_0(sK0)),X7) | u1_struct_0(sK0) = X7 | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X6))) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f58,f197])).
% 1.73/0.60  fof(f643,plain,(
% 1.73/0.60    ~spl8_7 | spl8_52 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f634,f403,f641,f124])).
% 1.73/0.60  fof(f641,plain,(
% 1.73/0.60    spl8_52 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1,X1),X1) | v1_xboole_0(X1) | sK1 = X1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 1.73/0.60  fof(f634,plain,(
% 1.73/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X1 | v1_xboole_0(X1) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1,X1),X1)) ) | ~spl8_32),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f628])).
% 1.73/0.60  fof(f628,plain,(
% 1.73/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X1 | v1_xboole_0(X1) | ~m1_subset_1(sK2(u1_struct_0(sK0),sK1,X1),X1)) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f463,f290])).
% 1.73/0.60  fof(f639,plain,(
% 1.73/0.60    spl8_51 | ~spl8_7 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f635,f403,f124,f637])).
% 1.73/0.60  fof(f635,plain,(
% 1.73/0.60    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0)) ) | ~spl8_32),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f627])).
% 1.73/0.60  fof(f627,plain,(
% 1.73/0.60    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(u1_struct_0(sK0),X0,sK1),X0) | sK1 = X0) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f463,f58])).
% 1.73/0.60  fof(f597,plain,(
% 1.73/0.60    ~spl8_1 | spl8_50 | ~spl8_48),
% 1.73/0.60    inference(avatar_split_clause,[],[f586,f579,f595,f94])).
% 1.73/0.60  fof(f94,plain,(
% 1.73/0.60    spl8_1 <=> l1_orders_2(sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.73/0.60  fof(f595,plain,(
% 1.73/0.60    spl8_50 <=> ! [X7,X8] : (~m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0)) | k1_yellow_0(sK0,X8) = k1_yellow_0(sK0,X7) | ~r2_lattice3(sK0,X7,k1_yellow_0(sK0,X8)) | ~r1_yellow_0(sK0,X7) | ~r1_yellow_0(sK0,X8) | ~r2_lattice3(sK0,sK1,sK7(sK0,X7,k1_yellow_0(sK0,X8))))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 1.73/0.60  fof(f579,plain,(
% 1.73/0.60    spl8_48 <=> ! [X3,X4] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_lattice3(sK0,X4,X3) | ~r2_lattice3(sK0,sK1,X3))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 1.73/0.60  fof(f586,plain,(
% 1.73/0.60    ( ! [X8,X7] : (~m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK1,sK7(sK0,X7,k1_yellow_0(sK0,X8))) | ~r1_yellow_0(sK0,X8) | ~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X7) | ~r2_lattice3(sK0,X7,k1_yellow_0(sK0,X8)) | k1_yellow_0(sK0,X8) = k1_yellow_0(sK0,X7)) ) | ~spl8_48),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f585])).
% 1.73/0.60  fof(f585,plain,(
% 1.73/0.60    ( ! [X8,X7] : (~m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK1,sK7(sK0,X7,k1_yellow_0(sK0,X8))) | ~m1_subset_1(sK7(sK0,X7,k1_yellow_0(sK0,X8)),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X8) | ~l1_orders_2(sK0) | ~r1_yellow_0(sK0,X7) | ~r2_lattice3(sK0,X7,k1_yellow_0(sK0,X8)) | k1_yellow_0(sK0,X8) = k1_yellow_0(sK0,X7)) ) | ~spl8_48),
% 1.73/0.60    inference(resolution,[],[f580,f313])).
% 1.73/0.60  fof(f313,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r2_lattice3(X0,X1,sK7(X0,X2,k1_yellow_0(X0,X1))) | ~m1_subset_1(sK7(X0,X2,k1_yellow_0(X0,X1)),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,k1_yellow_0(X0,X1)) | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)) )),
% 1.73/0.60    inference(global_subsumption,[],[f79,f312])).
% 1.73/0.60  fof(f312,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(sK7(X0,X2,k1_yellow_0(X0,X1)),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,sK7(X0,X2,k1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,k1_yellow_0(X0,X1)) | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)) )),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f309])).
% 1.73/0.60  fof(f309,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(sK7(X0,X2,k1_yellow_0(X0,X1)),u1_struct_0(X0)) | ~r2_lattice3(X0,X1,sK7(X0,X2,k1_yellow_0(X0,X1))) | ~l1_orders_2(X0) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X2) | ~r2_lattice3(X0,X2,k1_yellow_0(X0,X1)) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = k1_yellow_0(X0,X2)) )),
% 1.73/0.60    inference(resolution,[],[f92,f85])).
% 1.73/0.60  fof(f85,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f40,plain,(
% 1.73/0.60    ! [X0] : (! [X1,X2] : ((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(flattening,[],[f39])).
% 1.73/0.60  fof(f39,plain,(
% 1.73/0.60    ! [X0] : (! [X1,X2] : (((k1_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_lattice3(X0,X1,X2))) | ~r1_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f12])).
% 1.73/0.60  fof(f12,axiom,(
% 1.73/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_yellow_0(X0,X1) => (k1_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X3) => r1_orders_2(X0,X2,X3))) & r2_lattice3(X0,X1,X2))))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).
% 1.73/0.60  fof(f92,plain,(
% 1.73/0.60    ( ! [X0,X3,X1] : (r1_orders_2(X0,k1_yellow_0(X0,X1),X3) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(equality_resolution,[],[f86])).
% 1.73/0.60  fof(f86,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X3) | r1_orders_2(X0,X2,X3) | k1_yellow_0(X0,X1) != X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f79,plain,(
% 1.73/0.60    ( ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f38])).
% 1.73/0.60  fof(f38,plain,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f13])).
% 1.73/0.60  fof(f13,axiom,(
% 1.73/0.60    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).
% 1.73/0.60  fof(f580,plain,(
% 1.73/0.60    ( ! [X4,X3] : (r2_lattice3(sK0,X4,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK1,X3)) ) | ~spl8_48),
% 1.73/0.60    inference(avatar_component_clause,[],[f579])).
% 1.73/0.60  fof(f593,plain,(
% 1.73/0.60    ~spl8_1 | spl8_49 | ~spl8_48),
% 1.73/0.60    inference(avatar_split_clause,[],[f587,f579,f591,f94])).
% 1.73/0.60  fof(f591,plain,(
% 1.73/0.60    spl8_49 <=> ! [X5,X4,X6] : (~m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,X6) | k1_yellow_0(sK0,X4) = X5 | ~r2_lattice3(sK0,X4,X5) | ~r1_yellow_0(sK0,X4) | ~r2_lattice3(sK0,sK1,sK7(sK0,X4,X5)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 1.73/0.60  fof(f587,plain,(
% 1.73/0.60    ( ! [X6,X4,X5] : (~m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK1,sK7(sK0,X4,X5)) | ~r1_yellow_0(sK0,X4) | ~r2_lattice3(sK0,X4,X5) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,X4) = X5 | ~r2_hidden(X5,X6) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | ~spl8_48),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f584])).
% 1.73/0.60  fof(f584,plain,(
% 1.73/0.60    ( ! [X6,X4,X5] : (~m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0)) | ~r2_lattice3(sK0,sK1,sK7(sK0,X4,X5)) | ~r1_yellow_0(sK0,X4) | ~r2_lattice3(sK0,X4,X5) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,X4) = X5 | ~m1_subset_1(sK7(sK0,X4,X5),u1_struct_0(sK0)) | ~r2_hidden(X5,X6) | ~m1_subset_1(X5,u1_struct_0(sK0))) ) | ~spl8_48),
% 1.73/0.60    inference(resolution,[],[f580,f303])).
% 1.73/0.60  fof(f303,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~r2_lattice3(X1,X3,sK7(X1,X2,X0)) | ~r1_yellow_0(X1,X2) | ~r2_lattice3(X1,X2,X0) | ~l1_orders_2(X1) | k1_yellow_0(X1,X2) = X0 | ~m1_subset_1(sK7(X1,X2,X0),u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f302])).
% 1.73/0.60  fof(f302,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r1_yellow_0(X1,X2) | ~r2_lattice3(X1,X2,X0) | ~l1_orders_2(X1) | k1_yellow_0(X1,X2) = X0 | ~m1_subset_1(sK7(X1,X2,X0),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~l1_orders_2(X1) | ~r2_lattice3(X1,X3,sK7(X1,X2,X0))) )),
% 1.73/0.60    inference(resolution,[],[f85,f63])).
% 1.73/0.60  fof(f63,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | ~l1_orders_2(X0) | ~r2_lattice3(X0,X1,X2)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f32])).
% 1.73/0.60  fof(f32,plain,(
% 1.73/0.60    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(flattening,[],[f31])).
% 1.73/0.60  fof(f31,plain,(
% 1.73/0.60    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f10])).
% 1.73/0.60  fof(f10,axiom,(
% 1.73/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 1.73/0.60  fof(f581,plain,(
% 1.73/0.60    ~spl8_1 | spl8_48 | ~spl8_38),
% 1.73/0.60    inference(avatar_split_clause,[],[f576,f471,f579,f94])).
% 1.73/0.60  fof(f471,plain,(
% 1.73/0.60    spl8_38 <=> ! [X3,X2] : (r2_hidden(sK3(sK0,X2,X3),sK1) | r2_lattice3(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_38])])).
% 1.73/0.60  fof(f576,plain,(
% 1.73/0.60    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_lattice3(sK0,sK1,X3) | r2_lattice3(sK0,X4,X3)) ) | ~spl8_38),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f573])).
% 1.73/0.60  fof(f573,plain,(
% 1.73/0.60    ( ! [X4,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_lattice3(sK0,sK1,X3) | r2_lattice3(sK0,X4,X3) | r2_lattice3(sK0,X4,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl8_38),
% 1.73/0.60    inference(resolution,[],[f443,f472])).
% 1.73/0.60  fof(f472,plain,(
% 1.73/0.60    ( ! [X2,X3] : (r2_hidden(sK3(sK0,X2,X3),sK1) | r2_lattice3(sK0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | ~spl8_38),
% 1.73/0.60    inference(avatar_component_clause,[],[f471])).
% 1.73/0.60  fof(f443,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK3(X1,X2,X0),X3) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~r2_lattice3(X1,X3,X0) | r2_lattice3(X1,X2,X0)) )),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f439])).
% 1.73/0.60  fof(f439,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(sK3(X1,X2,X0),X3) | ~l1_orders_2(X1) | ~r2_lattice3(X1,X3,X0) | r2_lattice3(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0)) )),
% 1.73/0.60    inference(resolution,[],[f282,f64])).
% 1.73/0.60  fof(f64,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f32])).
% 1.73/0.60  fof(f282,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3(X1,X2,X0),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(sK3(X1,X2,X0),X3) | ~l1_orders_2(X1) | ~r2_lattice3(X1,X3,X0) | r2_lattice3(X1,X2,X0)) )),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f281])).
% 1.73/0.60  fof(f281,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(sK3(X1,X2,X0),u1_struct_0(X1)) | ~r2_hidden(sK3(X1,X2,X0),X3) | ~l1_orders_2(X1) | ~r2_lattice3(X1,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | r2_lattice3(X1,X2,X0)) )),
% 1.73/0.60    inference(resolution,[],[f63,f66])).
% 1.73/0.60  fof(f66,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f32])).
% 1.73/0.60  fof(f549,plain,(
% 1.73/0.60    spl8_10 | spl8_47 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f540,f124,f547,f139])).
% 1.73/0.60  fof(f547,plain,(
% 1.73/0.60    spl8_47 <=> ! [X1,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | ~m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),X1) | v1_xboole_0(X1) | u1_struct_0(sK0) = X1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 1.73/0.60  fof(f540,plain,(
% 1.73/0.60    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | u1_struct_0(sK0) = X1 | v1_xboole_0(X1) | ~m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),X1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | v1_xboole_0(sK1) | ~m1_subset_1(sK2(X2,u1_struct_0(sK0),X1),sK1)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f422,f61])).
% 1.73/0.60  fof(f545,plain,(
% 1.73/0.60    spl8_10 | spl8_20 | spl8_46 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f541,f124,f543,f213,f139])).
% 1.73/0.60  fof(f543,plain,(
% 1.73/0.60    spl8_46 <=> ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0)) | ~m1_subset_1(sK2(X0,u1_struct_0(sK0),sK1),sK1))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 1.73/0.60  fof(f541,plain,(
% 1.73/0.60    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK1 = u1_struct_0(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK2(X0,u1_struct_0(sK0),sK1),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,u1_struct_0(sK0),sK1),u1_struct_0(sK0))) ) | ~spl8_7),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f539])).
% 1.73/0.60  fof(f539,plain,(
% 1.73/0.60    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK1 = u1_struct_0(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK2(X0,u1_struct_0(sK0),sK1),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0)) | ~m1_subset_1(sK1,k1_zfmisc_1(X0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X0)) | r2_hidden(sK2(X0,u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f422,f57])).
% 1.73/0.60  fof(f538,plain,(
% 1.73/0.60    ~spl8_1 | spl8_45 | ~spl8_43),
% 1.73/0.60    inference(avatar_split_clause,[],[f534,f515,f536,f94])).
% 1.73/0.60  fof(f536,plain,(
% 1.73/0.60    spl8_45 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.73/0.60  fof(f515,plain,(
% 1.73/0.60    spl8_43 <=> v13_waybel_0(u1_struct_0(sK0),sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).
% 1.73/0.60  fof(f534,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl8_43),
% 1.73/0.60    inference(resolution,[],[f517,f316])).
% 1.73/0.60  fof(f316,plain,(
% 1.73/0.60    ( ! [X6,X4,X5] : (~v13_waybel_0(u1_struct_0(X4),X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~r2_hidden(X5,u1_struct_0(X4)) | ~r1_orders_2(X4,X5,X6) | r2_hidden(X6,u1_struct_0(X4)) | ~l1_orders_2(X4)) )),
% 1.73/0.60    inference(resolution,[],[f71,f221])).
% 1.73/0.60  fof(f221,plain,(
% 1.73/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.73/0.60    inference(backward_demodulation,[],[f77,f217])).
% 1.73/0.60  fof(f71,plain,(
% 1.73/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f34])).
% 1.73/0.60  fof(f34,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(flattening,[],[f33])).
% 1.73/0.60  fof(f33,plain,(
% 1.73/0.60    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f16])).
% 1.73/0.60  fof(f16,axiom,(
% 1.73/0.60    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.73/0.60  fof(f517,plain,(
% 1.73/0.60    v13_waybel_0(u1_struct_0(sK0),sK0) | ~spl8_43),
% 1.73/0.60    inference(avatar_component_clause,[],[f515])).
% 1.73/0.60  fof(f533,plain,(
% 1.73/0.60    spl8_10 | spl8_44 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f528,f124,f531,f139])).
% 1.73/0.60  fof(f531,plain,(
% 1.73/0.60    spl8_44 <=> ! [X1,X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(sK2(X2,X1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | u1_struct_0(sK0) = X1 | ~r2_hidden(sK2(X2,X1,u1_struct_0(sK0)),X1))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 1.73/0.60  fof(f528,plain,(
% 1.73/0.60    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(sK2(X2,X1,u1_struct_0(sK0)),X1) | u1_struct_0(sK0) = X1 | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(X2)) | v1_xboole_0(sK1) | ~m1_subset_1(sK2(X2,X1,u1_struct_0(sK0)),sK1)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f291,f61])).
% 1.73/0.60  fof(f526,plain,(
% 1.73/0.60    spl8_42),
% 1.73/0.60    inference(avatar_contradiction_clause,[],[f525])).
% 1.73/0.60  fof(f525,plain,(
% 1.73/0.60    $false | spl8_42),
% 1.73/0.60    inference(resolution,[],[f513,f221])).
% 1.73/0.60  fof(f513,plain,(
% 1.73/0.60    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_42),
% 1.73/0.60    inference(avatar_component_clause,[],[f511])).
% 1.73/0.60  fof(f518,plain,(
% 1.73/0.60    ~spl8_1 | ~spl8_42 | spl8_43 | ~spl8_7 | ~spl8_40),
% 1.73/0.60    inference(avatar_split_clause,[],[f509,f479,f124,f515,f511,f94])).
% 1.73/0.60  fof(f479,plain,(
% 1.73/0.60    spl8_40 <=> ! [X5] : (r2_hidden(sK5(sK0,X5),sK1) | v13_waybel_0(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 1.73/0.60  fof(f509,plain,(
% 1.73/0.60    v13_waybel_0(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | (~spl8_7 | ~spl8_40)),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f505])).
% 1.73/0.60  fof(f505,plain,(
% 1.73/0.60    v13_waybel_0(u1_struct_0(sK0),sK0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v13_waybel_0(u1_struct_0(sK0),sK0) | (~spl8_7 | ~spl8_40)),
% 1.73/0.60    inference(resolution,[],[f480,f274])).
% 1.73/0.60  fof(f274,plain,(
% 1.73/0.60    ( ! [X1] : (~r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | v13_waybel_0(u1_struct_0(sK0),X1)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f197,f70])).
% 1.73/0.60  fof(f70,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | v13_waybel_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f34])).
% 1.73/0.60  fof(f480,plain,(
% 1.73/0.60    ( ! [X5] : (r2_hidden(sK5(sK0,X5),sK1) | v13_waybel_0(X5,sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_40),
% 1.73/0.60    inference(avatar_component_clause,[],[f479])).
% 1.73/0.60  fof(f485,plain,(
% 1.73/0.60    ~spl8_1 | spl8_41 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f462,f403,f483,f94])).
% 1.73/0.60  fof(f483,plain,(
% 1.73/0.60    spl8_41 <=> ! [X7,X6] : (r2_hidden(sK7(sK0,X6,X7),sK1) | k1_yellow_0(sK0,X6) = X7 | ~r2_lattice3(sK0,X6,X7) | ~r1_yellow_0(sK0,X6) | ~m1_subset_1(X7,u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.73/0.60  fof(f462,plain,(
% 1.73/0.60    ( ! [X6,X7] : (r2_hidden(sK7(sK0,X6,X7),sK1) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X6) | ~r2_lattice3(sK0,X6,X7) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,X6) = X7) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f404,f83])).
% 1.73/0.60  fof(f83,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f481,plain,(
% 1.73/0.60    ~spl8_1 | spl8_40 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f461,f403,f479,f94])).
% 1.73/0.60  fof(f461,plain,(
% 1.73/0.60    ( ! [X5] : (r2_hidden(sK5(sK0,X5),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v13_waybel_0(X5,sK0)) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f404,f67])).
% 1.73/0.60  fof(f67,plain,(
% 1.73/0.60    ( ! [X0,X1] : (m1_subset_1(sK5(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | v13_waybel_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f34])).
% 1.73/0.60  fof(f477,plain,(
% 1.73/0.60    ~spl8_1 | spl8_39 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f460,f403,f475,f94])).
% 1.73/0.60  fof(f475,plain,(
% 1.73/0.60    spl8_39 <=> ! [X4] : (r2_hidden(sK4(sK0,X4),sK1) | v13_waybel_0(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 1.73/0.60  fof(f460,plain,(
% 1.73/0.60    ( ! [X4] : (r2_hidden(sK4(sK0,X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v13_waybel_0(X4,sK0)) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f404,f72])).
% 1.73/0.60  fof(f72,plain,(
% 1.73/0.60    ( ! [X0,X1] : (m1_subset_1(sK4(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | v13_waybel_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f34])).
% 1.73/0.60  fof(f473,plain,(
% 1.73/0.60    ~spl8_1 | spl8_38 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f459,f403,f471,f94])).
% 1.73/0.60  fof(f459,plain,(
% 1.73/0.60    ( ! [X2,X3] : (r2_hidden(sK3(sK0,X2,X3),sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r2_lattice3(sK0,X2,X3)) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f404,f64])).
% 1.73/0.60  fof(f469,plain,(
% 1.73/0.60    ~spl8_1 | spl8_37 | ~spl8_32),
% 1.73/0.60    inference(avatar_split_clause,[],[f458,f403,f467,f94])).
% 1.73/0.60  fof(f467,plain,(
% 1.73/0.60    spl8_37 <=> ! [X1] : r2_hidden(k1_yellow_0(sK0,X1),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 1.73/0.60  fof(f458,plain,(
% 1.73/0.60    ( ! [X1] : (r2_hidden(k1_yellow_0(sK0,X1),sK1) | ~l1_orders_2(sK0)) ) | ~spl8_32),
% 1.73/0.60    inference(resolution,[],[f404,f79])).
% 1.73/0.60  fof(f437,plain,(
% 1.73/0.60    spl8_36 | ~spl8_34),
% 1.73/0.60    inference(avatar_split_clause,[],[f431,f411,f434])).
% 1.73/0.60  fof(f434,plain,(
% 1.73/0.60    spl8_36 <=> m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.73/0.60  fof(f411,plain,(
% 1.73/0.60    spl8_34 <=> r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 1.73/0.60  fof(f431,plain,(
% 1.73/0.60    m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),sK1) | ~spl8_34),
% 1.73/0.60    inference(resolution,[],[f413,f62])).
% 1.73/0.60  fof(f62,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f30])).
% 1.73/0.60  fof(f30,plain,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.73/0.60    inference(ennf_transformation,[],[f5])).
% 1.73/0.60  fof(f5,axiom,(
% 1.73/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.73/0.60  fof(f413,plain,(
% 1.73/0.60    r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1) | ~spl8_34),
% 1.73/0.60    inference(avatar_component_clause,[],[f411])).
% 1.73/0.60  fof(f430,plain,(
% 1.73/0.60    ~spl8_1 | ~spl8_29 | spl8_33),
% 1.73/0.60    inference(avatar_split_clause,[],[f427,f407,f362,f94])).
% 1.73/0.60  fof(f362,plain,(
% 1.73/0.60    spl8_29 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 1.73/0.60  fof(f407,plain,(
% 1.73/0.60    spl8_33 <=> m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.73/0.60  fof(f427,plain,(
% 1.73/0.60    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | spl8_33),
% 1.73/0.60    inference(superposition,[],[f409,f73])).
% 1.73/0.60  fof(f73,plain,(
% 1.73/0.60    ( ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f35])).
% 1.73/0.60  fof(f35,plain,(
% 1.73/0.60    ! [X0] : (k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f11])).
% 1.73/0.60  fof(f11,axiom,(
% 1.73/0.60    ! [X0] : (l1_orders_2(X0) => k3_yellow_0(X0) = k1_yellow_0(X0,k1_xboole_0))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).
% 1.73/0.60  fof(f409,plain,(
% 1.73/0.60    ~m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl8_33),
% 1.73/0.60    inference(avatar_component_clause,[],[f407])).
% 1.73/0.60  fof(f429,plain,(
% 1.73/0.60    ~spl8_1 | spl8_33),
% 1.73/0.60    inference(avatar_split_clause,[],[f426,f407,f94])).
% 1.73/0.60  fof(f426,plain,(
% 1.73/0.60    ~l1_orders_2(sK0) | spl8_33),
% 1.73/0.60    inference(resolution,[],[f409,f79])).
% 1.73/0.60  fof(f428,plain,(
% 1.73/0.60    ~spl8_34 | ~spl8_7 | spl8_33),
% 1.73/0.60    inference(avatar_split_clause,[],[f425,f407,f124,f411])).
% 1.73/0.60  fof(f425,plain,(
% 1.73/0.60    ~r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1) | (~spl8_7 | spl8_33)),
% 1.73/0.60    inference(resolution,[],[f409,f193])).
% 1.73/0.60  fof(f193,plain,(
% 1.73/0.60    ( ! [X5] : (m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f55,f126])).
% 1.73/0.60  fof(f55,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f23])).
% 1.73/0.60  fof(f23,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.73/0.60    inference(flattening,[],[f22])).
% 1.73/0.60  fof(f22,plain,(
% 1.73/0.60    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.73/0.60    inference(ennf_transformation,[],[f8])).
% 1.73/0.60  fof(f8,axiom,(
% 1.73/0.60    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.73/0.60  fof(f418,plain,(
% 1.73/0.60    ~spl8_1 | ~spl8_31 | spl8_35 | ~spl8_30),
% 1.73/0.60    inference(avatar_split_clause,[],[f399,f366,f416,f369,f94])).
% 1.73/0.60  fof(f369,plain,(
% 1.73/0.60    spl8_31 <=> r1_yellow_0(sK0,k1_xboole_0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.73/0.60  fof(f416,plain,(
% 1.73/0.60    spl8_35 <=> ! [X1] : (r2_hidden(sK7(sK0,k1_xboole_0,X1),sK1) | k1_yellow_0(sK0,k1_xboole_0) = X1 | ~r2_lattice3(sK0,k1_xboole_0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(sK7(sK0,k1_xboole_0,X1),u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.73/0.60  fof(f366,plain,(
% 1.73/0.60    spl8_30 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,sK1) | ~r2_lattice3(sK0,k1_xboole_0,X2))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 1.73/0.60  fof(f399,plain,(
% 1.73/0.60    ( ! [X1] : (r2_hidden(sK7(sK0,k1_xboole_0,X1),sK1) | ~m1_subset_1(sK7(sK0,k1_xboole_0,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~r2_lattice3(sK0,k1_xboole_0,X1) | ~l1_orders_2(sK0) | k1_yellow_0(sK0,k1_xboole_0) = X1) ) | ~spl8_30),
% 1.73/0.60    inference(resolution,[],[f367,f84])).
% 1.73/0.60  fof(f84,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,sK7(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k1_yellow_0(X0,X1) = X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f367,plain,(
% 1.73/0.60    ( ! [X2] : (~r2_lattice3(sK0,k1_xboole_0,X2) | r2_hidden(X2,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl8_30),
% 1.73/0.60    inference(avatar_component_clause,[],[f366])).
% 1.73/0.60  fof(f414,plain,(
% 1.73/0.60    ~spl8_1 | ~spl8_31 | ~spl8_33 | spl8_34 | ~spl8_30),
% 1.73/0.60    inference(avatar_split_clause,[],[f400,f366,f411,f407,f369,f94])).
% 1.73/0.60  fof(f400,plain,(
% 1.73/0.60    r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1) | ~m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0) | ~spl8_30),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f398])).
% 1.73/0.60  fof(f398,plain,(
% 1.73/0.60    r2_hidden(k1_yellow_0(sK0,k1_xboole_0),sK1) | ~m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,k1_xboole_0) | ~l1_orders_2(sK0) | ~spl8_30),
% 1.73/0.60    inference(resolution,[],[f367,f91])).
% 1.73/0.60  fof(f91,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) | ~m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(equality_resolution,[],[f87])).
% 1.73/0.60  fof(f87,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_yellow_0(X0,X1) | r2_lattice3(X0,X1,X2) | k1_yellow_0(X0,X1) != X2) )),
% 1.73/0.60    inference(cnf_transformation,[],[f40])).
% 1.73/0.60  fof(f405,plain,(
% 1.73/0.60    ~spl8_1 | spl8_32 | ~spl8_30),
% 1.73/0.60    inference(avatar_split_clause,[],[f401,f366,f403,f94])).
% 1.73/0.60  fof(f401,plain,(
% 1.73/0.60    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0)) ) | ~spl8_30),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f397])).
% 1.73/0.60  fof(f397,plain,(
% 1.73/0.60    ( ! [X0] : (r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl8_30),
% 1.73/0.60    inference(resolution,[],[f367,f265])).
% 1.73/0.60  fof(f265,plain,(
% 1.73/0.60    ( ! [X4,X3] : (r2_lattice3(X4,k1_xboole_0,X3) | ~l1_orders_2(X4) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 1.73/0.60    inference(resolution,[],[f65,f190])).
% 1.73/0.60  fof(f190,plain,(
% 1.73/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.73/0.60    inference(resolution,[],[f154,f56])).
% 1.73/0.60  fof(f56,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f24])).
% 1.73/0.60  fof(f24,plain,(
% 1.73/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.73/0.60    inference(ennf_transformation,[],[f9])).
% 1.73/0.60  fof(f9,axiom,(
% 1.73/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.73/0.60  fof(f154,plain,(
% 1.73/0.60    ( ! [X2] : (r1_tarski(k1_xboole_0,X2)) )),
% 1.73/0.60    inference(resolution,[],[f82,f80])).
% 1.73/0.60  fof(f80,plain,(
% 1.73/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.73/0.60    inference(cnf_transformation,[],[f2])).
% 1.73/0.60  fof(f2,axiom,(
% 1.73/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.73/0.60  fof(f82,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f7])).
% 1.73/0.60  fof(f7,axiom,(
% 1.73/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.73/0.60  fof(f65,plain,(
% 1.73/0.60    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_lattice3(X0,X1,X2)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f32])).
% 1.73/0.60  fof(f382,plain,(
% 1.73/0.60    spl8_6 | ~spl8_1 | ~spl8_2 | ~spl8_3 | spl8_31),
% 1.73/0.60    inference(avatar_split_clause,[],[f381,f369,f104,f99,f94,f119])).
% 1.73/0.60  fof(f119,plain,(
% 1.73/0.60    spl8_6 <=> v2_struct_0(sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.73/0.60  fof(f99,plain,(
% 1.73/0.60    spl8_2 <=> v1_yellow_0(sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.73/0.60  fof(f104,plain,(
% 1.73/0.60    spl8_3 <=> v5_orders_2(sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.73/0.60  fof(f381,plain,(
% 1.73/0.60    ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | spl8_31),
% 1.73/0.60    inference(resolution,[],[f371,f88])).
% 1.73/0.60  fof(f88,plain,(
% 1.73/0.60    ( ! [X0] : (r1_yellow_0(X0,k1_xboole_0) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f42])).
% 1.73/0.60  fof(f42,plain,(
% 1.73/0.60    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.73/0.60    inference(flattening,[],[f41])).
% 1.73/0.60  fof(f41,plain,(
% 1.73/0.60    ! [X0] : ((r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f15])).
% 1.73/0.60  fof(f15,axiom,(
% 1.73/0.60    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => (r2_yellow_0(X0,u1_struct_0(X0)) & r1_yellow_0(X0,k1_xboole_0)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_yellow_0)).
% 1.73/0.60  fof(f371,plain,(
% 1.73/0.60    ~r1_yellow_0(sK0,k1_xboole_0) | spl8_31),
% 1.73/0.60    inference(avatar_component_clause,[],[f369])).
% 1.73/0.60  fof(f376,plain,(
% 1.73/0.60    ~spl8_1 | spl8_29),
% 1.73/0.60    inference(avatar_split_clause,[],[f374,f362,f94])).
% 1.73/0.60  fof(f374,plain,(
% 1.73/0.60    ~l1_orders_2(sK0) | spl8_29),
% 1.73/0.60    inference(resolution,[],[f364,f74])).
% 1.73/0.60  fof(f74,plain,(
% 1.73/0.60    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f36])).
% 1.73/0.60  fof(f36,plain,(
% 1.73/0.60    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.73/0.60    inference(ennf_transformation,[],[f14])).
% 1.73/0.60  fof(f14,axiom,(
% 1.73/0.60    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.73/0.60  fof(f364,plain,(
% 1.73/0.60    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl8_29),
% 1.73/0.60    inference(avatar_component_clause,[],[f362])).
% 1.73/0.60  fof(f375,plain,(
% 1.73/0.60    ~spl8_12 | ~spl8_7 | spl8_29),
% 1.73/0.60    inference(avatar_split_clause,[],[f373,f362,f124,f148])).
% 1.73/0.60  fof(f148,plain,(
% 1.73/0.60    spl8_12 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 1.73/0.60  fof(f373,plain,(
% 1.73/0.60    ~r2_hidden(k3_yellow_0(sK0),sK1) | (~spl8_7 | spl8_29)),
% 1.73/0.60    inference(resolution,[],[f364,f193])).
% 1.73/0.60  fof(f372,plain,(
% 1.73/0.60    ~spl8_12 | ~spl8_29 | ~spl8_1 | spl8_30 | ~spl8_31 | ~spl8_25),
% 1.73/0.60    inference(avatar_split_clause,[],[f359,f321,f369,f366,f94,f362,f148])).
% 1.73/0.60  fof(f321,plain,(
% 1.73/0.60    spl8_25 <=> ! [X11,X10] : (~m1_subset_1(X10,u1_struct_0(sK0)) | r2_hidden(X11,sK1) | ~r1_orders_2(sK0,X10,X11) | ~r2_hidden(X10,sK1) | ~m1_subset_1(X11,u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.73/0.60  fof(f359,plain,(
% 1.73/0.60    ( ! [X2] : (~r1_yellow_0(sK0,k1_xboole_0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X2) | ~l1_orders_2(sK0) | r2_hidden(X2,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1)) ) | ~spl8_25),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f358])).
% 1.73/0.60  fof(f358,plain,(
% 1.73/0.60    ( ! [X2] : (~r1_yellow_0(sK0,k1_xboole_0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,k1_xboole_0,X2) | ~l1_orders_2(sK0) | r2_hidden(X2,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl8_25),
% 1.73/0.60    inference(resolution,[],[f314,f322])).
% 1.73/0.60  fof(f322,plain,(
% 1.73/0.60    ( ! [X10,X11] : (~r1_orders_2(sK0,X10,X11) | r2_hidden(X11,sK1) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~r2_hidden(X10,sK1) | ~m1_subset_1(X11,u1_struct_0(sK0))) ) | ~spl8_25),
% 1.73/0.60    inference(avatar_component_clause,[],[f321])).
% 1.73/0.60  fof(f314,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~r1_yellow_0(X0,k1_xboole_0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,k1_xboole_0,X1) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(global_subsumption,[],[f74,f311])).
% 1.73/0.60  fof(f311,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~r1_yellow_0(X0,k1_xboole_0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,k1_xboole_0,X1) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f310])).
% 1.73/0.60  fof(f310,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~r1_yellow_0(X0,k1_xboole_0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r2_lattice3(X0,k1_xboole_0,X1) | ~l1_orders_2(X0) | ~l1_orders_2(X0)) )),
% 1.73/0.60    inference(superposition,[],[f92,f73])).
% 1.73/0.60  fof(f340,plain,(
% 1.73/0.60    ~spl8_1 | spl8_28 | ~spl8_25),
% 1.73/0.60    inference(avatar_split_clause,[],[f327,f321,f338,f94])).
% 1.73/0.60  fof(f338,plain,(
% 1.73/0.60    spl8_28 <=> ! [X5,X4] : (r2_hidden(X4,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0)) | ~r2_lattice3(sK0,X5,X4) | ~r1_yellow_0(sK0,X5) | ~r2_hidden(k1_yellow_0(sK0,X5),sK1))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 1.73/0.60  fof(f327,plain,(
% 1.73/0.60    ( ! [X4,X5] : (r2_hidden(X4,sK1) | ~m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0)) | ~r2_hidden(k1_yellow_0(sK0,X5),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X5) | ~r2_lattice3(sK0,X5,X4) | ~l1_orders_2(sK0)) ) | ~spl8_25),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f326])).
% 1.73/0.60  fof(f326,plain,(
% 1.73/0.60    ( ! [X4,X5] : (r2_hidden(X4,sK1) | ~m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0)) | ~r2_hidden(k1_yellow_0(sK0,X5),sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(k1_yellow_0(sK0,X5),u1_struct_0(sK0)) | ~r1_yellow_0(sK0,X5) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X5,X4) | ~l1_orders_2(sK0)) ) | ~spl8_25),
% 1.73/0.60    inference(resolution,[],[f322,f92])).
% 1.73/0.60  fof(f336,plain,(
% 1.73/0.60    ~spl8_1 | spl8_27 | ~spl8_25),
% 1.73/0.60    inference(avatar_split_clause,[],[f328,f321,f334,f94])).
% 1.73/0.60  fof(f334,plain,(
% 1.73/0.60    spl8_27 <=> ! [X1,X3,X2] : (r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_lattice3(sK0,X3,X1) | ~r2_hidden(X2,X3) | ~r2_hidden(X2,sK1))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.73/0.60  fof(f328,plain,(
% 1.73/0.60    ( ! [X2,X3,X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X2,X3) | ~l1_orders_2(sK0) | ~r2_lattice3(sK0,X3,X1)) ) | ~spl8_25),
% 1.73/0.60    inference(duplicate_literal_removal,[],[f325])).
% 1.73/0.60  fof(f325,plain,(
% 1.73/0.60    ( ! [X2,X3,X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X3) | ~l1_orders_2(sK0) | ~r2_lattice3(sK0,X3,X1)) ) | ~spl8_25),
% 1.73/0.60    inference(resolution,[],[f322,f63])).
% 1.73/0.60  fof(f332,plain,(
% 1.73/0.60    ~spl8_1 | spl8_26 | ~spl8_25),
% 1.73/0.60    inference(avatar_split_clause,[],[f324,f321,f330,f94])).
% 1.73/0.60  fof(f330,plain,(
% 1.73/0.60    spl8_26 <=> ! [X0] : (r2_hidden(sK5(sK0,X0),sK1) | v13_waybel_0(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,X0),sK1) | ~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.73/0.60  fof(f324,plain,(
% 1.73/0.60    ( ! [X0] : (r2_hidden(sK5(sK0,X0),sK1) | ~m1_subset_1(sK4(sK0,X0),u1_struct_0(sK0)) | ~r2_hidden(sK4(sK0,X0),sK1) | ~m1_subset_1(sK5(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | v13_waybel_0(X0,sK0)) ) | ~spl8_25),
% 1.73/0.60    inference(resolution,[],[f322,f69])).
% 1.73/0.60  fof(f69,plain,(
% 1.73/0.60    ( ! [X0,X1] : (r1_orders_2(X0,sK4(X0,X1),sK5(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | v13_waybel_0(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f34])).
% 1.73/0.60  fof(f323,plain,(
% 1.73/0.60    ~spl8_8 | spl8_25 | ~spl8_1 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f318,f124,f94,f321,f129])).
% 1.73/0.60  fof(f129,plain,(
% 1.73/0.60    spl8_8 <=> v13_waybel_0(sK1,sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 1.73/0.60  fof(f318,plain,(
% 1.73/0.60    ( ! [X10,X11] : (~l1_orders_2(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~r2_hidden(X10,sK1) | ~r1_orders_2(sK0,X10,X11) | r2_hidden(X11,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f71,f126])).
% 1.73/0.60  fof(f308,plain,(
% 1.73/0.60    spl8_10 | spl8_24 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f304,f124,f306,f139])).
% 1.73/0.60  fof(f306,plain,(
% 1.73/0.60    spl8_24 <=> ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK5(X0,u1_struct_0(sK0)),sK1) | v13_waybel_0(u1_struct_0(sK0),X0) | ~l1_orders_2(X0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 1.73/0.60  fof(f304,plain,(
% 1.73/0.60    ( ! [X0] : (~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | v13_waybel_0(u1_struct_0(sK0),X0) | v1_xboole_0(sK1) | ~m1_subset_1(sK5(X0,u1_struct_0(sK0)),sK1)) ) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f274,f61])).
% 1.73/0.60  fof(f254,plain,(
% 1.73/0.60    spl8_16 | ~spl8_12),
% 1.73/0.60    inference(avatar_split_clause,[],[f253,f148,f179])).
% 1.73/0.60  fof(f179,plain,(
% 1.73/0.60    spl8_16 <=> m1_subset_1(k3_yellow_0(sK0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 1.73/0.60  fof(f253,plain,(
% 1.73/0.60    m1_subset_1(k3_yellow_0(sK0),sK1) | ~spl8_12),
% 1.73/0.60    inference(resolution,[],[f150,f62])).
% 1.73/0.60  fof(f150,plain,(
% 1.73/0.60    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl8_12),
% 1.73/0.60    inference(avatar_component_clause,[],[f148])).
% 1.73/0.60  fof(f252,plain,(
% 1.73/0.60    ~spl8_1 | spl8_16 | ~spl8_20),
% 1.73/0.60    inference(avatar_split_clause,[],[f247,f213,f179,f94])).
% 1.73/0.60  fof(f247,plain,(
% 1.73/0.60    m1_subset_1(k3_yellow_0(sK0),sK1) | ~l1_orders_2(sK0) | ~spl8_20),
% 1.73/0.60    inference(superposition,[],[f74,f215])).
% 1.73/0.60  fof(f251,plain,(
% 1.73/0.60    ~spl8_1 | spl8_23 | ~spl8_20),
% 1.73/0.60    inference(avatar_split_clause,[],[f246,f213,f249,f94])).
% 1.73/0.60  fof(f249,plain,(
% 1.73/0.60    spl8_23 <=> ! [X0] : m1_subset_1(k1_yellow_0(sK0,X0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 1.73/0.60  fof(f246,plain,(
% 1.73/0.60    ( ! [X0] : (m1_subset_1(k1_yellow_0(sK0,X0),sK1) | ~l1_orders_2(sK0)) ) | ~spl8_20),
% 1.73/0.60    inference(superposition,[],[f79,f215])).
% 1.73/0.60  fof(f239,plain,(
% 1.73/0.60    ~spl8_22 | spl8_17 | ~spl8_20),
% 1.73/0.60    inference(avatar_split_clause,[],[f227,f213,f184,f236])).
% 1.73/0.60  fof(f236,plain,(
% 1.73/0.60    spl8_22 <=> m1_subset_1(sK1,sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 1.73/0.60  fof(f184,plain,(
% 1.73/0.60    spl8_17 <=> m1_subset_1(u1_struct_0(sK0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 1.73/0.60  fof(f227,plain,(
% 1.73/0.60    ~m1_subset_1(sK1,sK1) | (spl8_17 | ~spl8_20)),
% 1.73/0.60    inference(backward_demodulation,[],[f186,f215])).
% 1.73/0.60  fof(f186,plain,(
% 1.73/0.60    ~m1_subset_1(u1_struct_0(sK0),sK1) | spl8_17),
% 1.73/0.60    inference(avatar_component_clause,[],[f184])).
% 1.73/0.60  fof(f234,plain,(
% 1.73/0.60    ~spl8_21 | spl8_14 | ~spl8_20),
% 1.73/0.60    inference(avatar_split_clause,[],[f226,f213,f164,f231])).
% 1.73/0.60  fof(f231,plain,(
% 1.73/0.60    spl8_21 <=> r2_hidden(sK1,sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.73/0.60  fof(f164,plain,(
% 1.73/0.60    spl8_14 <=> r2_hidden(u1_struct_0(sK0),sK1)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).
% 1.73/0.60  fof(f226,plain,(
% 1.73/0.60    ~r2_hidden(sK1,sK1) | (spl8_14 | ~spl8_20)),
% 1.73/0.60    inference(backward_demodulation,[],[f166,f215])).
% 1.73/0.60  fof(f166,plain,(
% 1.73/0.60    ~r2_hidden(u1_struct_0(sK0),sK1) | spl8_14),
% 1.73/0.60    inference(avatar_component_clause,[],[f164])).
% 1.73/0.60  fof(f216,plain,(
% 1.73/0.60    spl8_11 | spl8_20 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f210,f124,f213,f144])).
% 1.73/0.60  fof(f210,plain,(
% 1.73/0.60    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f75,f126])).
% 1.73/0.60  fof(f207,plain,(
% 1.73/0.60    spl8_18 | spl8_19),
% 1.73/0.60    inference(avatar_split_clause,[],[f199,f204,f201])).
% 1.73/0.60  fof(f201,plain,(
% 1.73/0.60    spl8_18 <=> ! [X0] : ~m1_subset_1(X0,k1_xboole_0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.73/0.60  fof(f204,plain,(
% 1.73/0.60    spl8_19 <=> v1_xboole_0(k1_xboole_0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 1.73/0.60  fof(f199,plain,(
% 1.73/0.60    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(X0,k1_xboole_0)) )),
% 1.73/0.60    inference(resolution,[],[f190,f61])).
% 1.73/0.60  fof(f187,plain,(
% 1.73/0.60    ~spl8_17 | spl8_10 | spl8_14),
% 1.73/0.60    inference(avatar_split_clause,[],[f177,f164,f139,f184])).
% 1.73/0.60  fof(f177,plain,(
% 1.73/0.60    v1_xboole_0(sK1) | ~m1_subset_1(u1_struct_0(sK0),sK1) | spl8_14),
% 1.73/0.60    inference(resolution,[],[f61,f166])).
% 1.73/0.60  fof(f182,plain,(
% 1.73/0.60    ~spl8_16 | spl8_10 | spl8_12),
% 1.73/0.60    inference(avatar_split_clause,[],[f175,f148,f139,f179])).
% 1.73/0.60  fof(f175,plain,(
% 1.73/0.60    v1_xboole_0(sK1) | ~m1_subset_1(k3_yellow_0(sK0),sK1) | spl8_12),
% 1.73/0.60    inference(resolution,[],[f61,f149])).
% 1.73/0.60  fof(f149,plain,(
% 1.73/0.60    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl8_12),
% 1.73/0.60    inference(avatar_component_clause,[],[f148])).
% 1.73/0.60  fof(f174,plain,(
% 1.73/0.60    ~spl8_15),
% 1.73/0.60    inference(avatar_split_clause,[],[f169,f171])).
% 1.73/0.60  fof(f171,plain,(
% 1.73/0.60    spl8_15 <=> v1_subset_1(k1_xboole_0,k1_xboole_0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 1.73/0.60  fof(f169,plain,(
% 1.73/0.60    ~v1_subset_1(k1_xboole_0,k1_xboole_0)),
% 1.73/0.60    inference(resolution,[],[f90,f80])).
% 1.73/0.60  fof(f90,plain,(
% 1.73/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.73/0.60    inference(equality_resolution,[],[f76])).
% 1.73/0.60  fof(f76,plain,(
% 1.73/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.73/0.60    inference(cnf_transformation,[],[f37])).
% 1.73/0.60  fof(f167,plain,(
% 1.73/0.60    ~spl8_14 | ~spl8_13),
% 1.73/0.60    inference(avatar_split_clause,[],[f162,f158,f164])).
% 1.73/0.60  fof(f158,plain,(
% 1.73/0.60    spl8_13 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 1.73/0.60  fof(f162,plain,(
% 1.73/0.60    ~r2_hidden(u1_struct_0(sK0),sK1) | ~spl8_13),
% 1.73/0.60    inference(resolution,[],[f160,f56])).
% 1.73/0.60  fof(f160,plain,(
% 1.73/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl8_13),
% 1.73/0.60    inference(avatar_component_clause,[],[f158])).
% 1.73/0.60  fof(f161,plain,(
% 1.73/0.60    spl8_13 | ~spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f155,f124,f158])).
% 1.73/0.60  fof(f155,plain,(
% 1.73/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl8_7),
% 1.73/0.60    inference(resolution,[],[f82,f126])).
% 1.73/0.60  fof(f152,plain,(
% 1.73/0.60    spl8_11 | ~spl8_12),
% 1.73/0.60    inference(avatar_split_clause,[],[f43,f148,f144])).
% 1.73/0.60  fof(f43,plain,(
% 1.73/0.60    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f21,plain,(
% 1.73/0.60    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.73/0.60    inference(flattening,[],[f20])).
% 1.73/0.60  fof(f20,plain,(
% 1.73/0.60    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.73/0.60    inference(ennf_transformation,[],[f19])).
% 1.73/0.60  fof(f19,negated_conjecture,(
% 1.73/0.60    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.73/0.60    inference(negated_conjecture,[],[f18])).
% 1.73/0.60  fof(f18,conjecture,(
% 1.73/0.60    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.73/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.73/0.60  fof(f151,plain,(
% 1.73/0.60    ~spl8_11 | spl8_12),
% 1.73/0.60    inference(avatar_split_clause,[],[f44,f148,f144])).
% 1.73/0.60  fof(f44,plain,(
% 1.73/0.60    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f142,plain,(
% 1.73/0.60    ~spl8_10),
% 1.73/0.60    inference(avatar_split_clause,[],[f45,f139])).
% 1.73/0.60  fof(f45,plain,(
% 1.73/0.60    ~v1_xboole_0(sK1)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f137,plain,(
% 1.73/0.60    spl8_9),
% 1.73/0.60    inference(avatar_split_clause,[],[f46,f134])).
% 1.73/0.60  fof(f134,plain,(
% 1.73/0.60    spl8_9 <=> v2_waybel_0(sK1,sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.73/0.60  fof(f46,plain,(
% 1.73/0.60    v2_waybel_0(sK1,sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f132,plain,(
% 1.73/0.60    spl8_8),
% 1.73/0.60    inference(avatar_split_clause,[],[f47,f129])).
% 1.73/0.60  fof(f47,plain,(
% 1.73/0.60    v13_waybel_0(sK1,sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f127,plain,(
% 1.73/0.60    spl8_7),
% 1.73/0.60    inference(avatar_split_clause,[],[f48,f124])).
% 1.73/0.60  fof(f48,plain,(
% 1.73/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f122,plain,(
% 1.73/0.60    ~spl8_6),
% 1.73/0.60    inference(avatar_split_clause,[],[f49,f119])).
% 1.73/0.60  fof(f49,plain,(
% 1.73/0.60    ~v2_struct_0(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f117,plain,(
% 1.73/0.60    spl8_5),
% 1.73/0.60    inference(avatar_split_clause,[],[f50,f114])).
% 1.73/0.60  fof(f114,plain,(
% 1.73/0.60    spl8_5 <=> v3_orders_2(sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.73/0.60  fof(f50,plain,(
% 1.73/0.60    v3_orders_2(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f112,plain,(
% 1.73/0.60    spl8_4),
% 1.73/0.60    inference(avatar_split_clause,[],[f51,f109])).
% 1.73/0.60  fof(f109,plain,(
% 1.73/0.60    spl8_4 <=> v4_orders_2(sK0)),
% 1.73/0.60    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.73/0.60  fof(f51,plain,(
% 1.73/0.60    v4_orders_2(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f107,plain,(
% 1.73/0.60    spl8_3),
% 1.73/0.60    inference(avatar_split_clause,[],[f52,f104])).
% 1.73/0.60  fof(f52,plain,(
% 1.73/0.60    v5_orders_2(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f102,plain,(
% 1.73/0.60    spl8_2),
% 1.73/0.60    inference(avatar_split_clause,[],[f53,f99])).
% 1.73/0.60  fof(f53,plain,(
% 1.73/0.60    v1_yellow_0(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  fof(f97,plain,(
% 1.73/0.60    spl8_1),
% 1.73/0.60    inference(avatar_split_clause,[],[f54,f94])).
% 1.73/0.60  fof(f54,plain,(
% 1.73/0.60    l1_orders_2(sK0)),
% 1.73/0.60    inference(cnf_transformation,[],[f21])).
% 1.73/0.60  % SZS output end Proof for theBenchmark
% 1.73/0.60  % (32220)------------------------------
% 1.73/0.60  % (32220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.60  % (32220)Termination reason: Refutation
% 1.73/0.60  
% 1.73/0.60  % (32220)Memory used [KB]: 6652
% 1.73/0.60  % (32220)Time elapsed: 0.182 s
% 1.73/0.60  % (32220)------------------------------
% 1.73/0.60  % (32220)------------------------------
% 1.73/0.60  % (32202)Success in time 0.251 s
%------------------------------------------------------------------------------
