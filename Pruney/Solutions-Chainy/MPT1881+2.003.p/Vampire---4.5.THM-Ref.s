%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:52 EST 2020

% Result     : Theorem 3.66s
% Output     : Refutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :  271 ( 721 expanded)
%              Number of leaves         :   59 ( 307 expanded)
%              Depth                    :   15
%              Number of atoms          : 1061 (3044 expanded)
%              Number of equality atoms :   66 ( 174 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f128,f133,f138,f147,f149,f154,f160,f204,f233,f261,f286,f292,f314,f371,f394,f420,f452,f546,f683,f688,f710,f715,f716,f717,f752,f760,f976,f981,f1023,f2326,f2997,f3315,f3669,f4141,f4193])).

fof(f4193,plain,
    ( spl7_16
    | ~ spl7_28
    | spl7_45
    | ~ spl7_49
    | ~ spl7_107
    | ~ spl7_118 ),
    inference(avatar_contradiction_clause,[],[f4192])).

fof(f4192,plain,
    ( $false
    | spl7_16
    | ~ spl7_28
    | spl7_45
    | ~ spl7_49
    | ~ spl7_107
    | ~ spl7_118 ),
    inference(subsumption_resolution,[],[f4164,f4170])).

fof(f4170,plain,
    ( r2_hidden(sK6(sK1,sK2(sK0,sK1),sK1),sK2(sK0,sK1))
    | spl7_16
    | ~ spl7_107
    | ~ spl7_118 ),
    inference(unit_resulting_resolution,[],[f313,f3668,f4140,f213])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f104,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f4140,plain,
    ( m1_subset_1(sK6(sK1,sK2(sK0,sK1),sK1),sK1)
    | ~ spl7_118 ),
    inference(avatar_component_clause,[],[f4138])).

fof(f4138,plain,
    ( spl7_118
  <=> m1_subset_1(sK6(sK1,sK2(sK0,sK1),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).

fof(f3668,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl7_107 ),
    inference(avatar_component_clause,[],[f3666])).

fof(f3666,plain,
    ( spl7_107
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).

fof(f313,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl7_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f4164,plain,
    ( ~ r2_hidden(sK6(sK1,sK2(sK0,sK1),sK1),sK2(sK0,sK1))
    | spl7_16
    | ~ spl7_28
    | spl7_45
    | ~ spl7_49
    | ~ spl7_118 ),
    inference(unit_resulting_resolution,[],[f313,f687,f975,f1022,f4140,f256])).

fof(f256,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X2,X0,X1),X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | ~ m1_subset_1(sK6(X2,X0,X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f107,f97])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK6(X0,X1,X2),X2)
              | ~ r2_hidden(sK6(X0,X1,X2),X1) )
            & ( r2_hidden(sK6(X0,X1,X2),X2)
              | r2_hidden(sK6(X0,X1,X2),X1) )
            & m1_subset_1(sK6(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK6(X0,X1,X2),X2)
          | ~ r2_hidden(sK6(X0,X1,X2),X1) )
        & ( r2_hidden(sK6(X0,X1,X2),X2)
          | r2_hidden(sK6(X0,X1,X2),X1) )
        & m1_subset_1(sK6(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f1022,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f1020])).

fof(f1020,plain,
    ( spl7_49
  <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f975,plain,
    ( sK1 != sK2(sK0,sK1)
    | spl7_45 ),
    inference(avatar_component_clause,[],[f973])).

fof(f973,plain,
    ( spl7_45
  <=> sK1 = sK2(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f687,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f685])).

fof(f685,plain,
    ( spl7_28
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f4141,plain,
    ( spl7_118
    | ~ spl7_28
    | spl7_45
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f1031,f1020,f973,f685,f4138])).

fof(f1031,plain,
    ( m1_subset_1(sK6(sK1,sK2(sK0,sK1),sK1),sK1)
    | ~ spl7_28
    | spl7_45
    | ~ spl7_49 ),
    inference(unit_resulting_resolution,[],[f687,f975,f1022,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),X0)
      | X1 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f3669,plain,
    ( spl7_107
    | ~ spl7_46 ),
    inference(avatar_split_clause,[],[f988,f978,f3666])).

fof(f978,plain,
    ( spl7_46
  <=> r1_tarski(sK1,sK2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f988,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | ~ spl7_46 ),
    inference(unit_resulting_resolution,[],[f980,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f980,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl7_46 ),
    inference(avatar_component_clause,[],[f978])).

fof(f3315,plain,
    ( ~ spl7_9
    | ~ spl7_16
    | spl7_89
    | ~ spl7_104 ),
    inference(avatar_contradiction_clause,[],[f3314])).

fof(f3314,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_16
    | spl7_89
    | ~ spl7_104 ),
    inference(subsumption_resolution,[],[f3300,f2996])).

fof(f2996,plain,
    ( m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1))
    | ~ spl7_104 ),
    inference(avatar_component_clause,[],[f2994])).

fof(f2994,plain,
    ( spl7_104
  <=> m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).

fof(f3300,plain,
    ( ~ m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1))
    | ~ spl7_9
    | ~ spl7_16
    | spl7_89 ),
    inference(unit_resulting_resolution,[],[f2325,f312,f493])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl7_9 ),
    inference(condensation,[],[f489])).

fof(f489,plain,
    ( ! [X10,X8,X9] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | k1_xboole_0 = X8
        | ~ m1_subset_1(X8,k1_zfmisc_1(X10))
        | ~ v1_xboole_0(X10) )
    | ~ spl7_9 ),
    inference(resolution,[],[f251,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f251,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(X0,k1_xboole_0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k1_xboole_0 = X1 )
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f243,f196])).

fof(f196,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f159,f78,f111])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f159,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl7_9
  <=> v1_xboole_0(sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f243,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,k1_xboole_0,X1),X1)
      | r2_hidden(sK6(X0,k1_xboole_0,X1),k1_xboole_0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f106,f78])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f312,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f311])).

fof(f2325,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | spl7_89 ),
    inference(avatar_component_clause,[],[f2323])).

fof(f2323,plain,
    ( spl7_89
  <=> k1_xboole_0 = sK2(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).

fof(f2997,plain,
    ( spl7_104
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_27
    | ~ spl7_31
    | spl7_32 ),
    inference(avatar_split_clause,[],[f827,f712,f707,f680,f368,f296,f157,f151,f130,f2994])).

fof(f130,plain,
    ( spl7_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f151,plain,
    ( spl7_8
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f296,plain,
    ( spl7_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f368,plain,
    ( spl7_21
  <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f680,plain,
    ( spl7_27
  <=> m1_subset_1(k1_xboole_0,sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f707,plain,
    ( spl7_31
  <=> v2_tex_2(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f712,plain,
    ( spl7_32
  <=> v3_tex_2(sK3(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f827,plain,
    ( m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1))
    | ~ spl7_4
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_27
    | ~ spl7_31
    | spl7_32 ),
    inference(forward_demodulation,[],[f826,f776])).

fof(f776,plain,
    ( k1_xboole_0 = sK3(sK0)
    | ~ spl7_8
    | ~ spl7_9
    | ~ spl7_27 ),
    inference(subsumption_resolution,[],[f775,f182])).

fof(f182,plain,
    ( ! [X0] : ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(sK3(sK0)))
    | ~ spl7_9 ),
    inference(unit_resulting_resolution,[],[f77,f159,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f77,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f775,plain,
    ( k1_xboole_0 = sK3(sK0)
    | m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK3(sK0)))
    | ~ spl7_8
    | ~ spl7_27 ),
    inference(resolution,[],[f682,f217])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,X0)
        | k1_xboole_0 = X0
        | m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0)) )
    | ~ spl7_8 ),
    inference(superposition,[],[f101,f153])).

fof(f153,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f151])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

fof(f682,plain,
    ( m1_subset_1(k1_xboole_0,sK3(sK0))
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f680])).

fof(f826,plain,
    ( m1_subset_1(sK2(sK0,sK3(sK0)),k1_zfmisc_1(sK1))
    | ~ spl7_4
    | ~ spl7_15
    | ~ spl7_21
    | ~ spl7_31
    | spl7_32 ),
    inference(forward_demodulation,[],[f819,f298])).

fof(f298,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f296])).

fof(f819,plain,
    ( m1_subset_1(sK2(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_4
    | ~ spl7_21
    | ~ spl7_31
    | spl7_32 ),
    inference(unit_resulting_resolution,[],[f132,f709,f370,f714,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f714,plain,
    ( ~ v3_tex_2(sK3(sK0),sK0)
    | spl7_32 ),
    inference(avatar_component_clause,[],[f712])).

fof(f370,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f368])).

fof(f709,plain,
    ( v2_tex_2(sK3(sK0),sK0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f707])).

fof(f132,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f2326,plain,
    ( ~ spl7_89
    | ~ spl7_4
    | ~ spl7_12
    | spl7_22 ),
    inference(avatar_split_clause,[],[f620,f391,f258,f130,f2323])).

fof(f258,plain,
    ( spl7_12
  <=> v2_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f391,plain,
    ( spl7_22
  <=> v3_tex_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f620,plain,
    ( k1_xboole_0 != sK2(sK0,k1_xboole_0)
    | ~ spl7_4
    | ~ spl7_12
    | spl7_22 ),
    inference(unit_resulting_resolution,[],[f132,f260,f78,f393,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f393,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK0)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f391])).

fof(f260,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f258])).

fof(f1023,plain,
    ( spl7_49
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f767,f296,f230,f140,f135,f130,f1020])).

fof(f135,plain,
    ( spl7_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f140,plain,
    ( spl7_6
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f230,plain,
    ( spl7_11
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f767,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f763,f298])).

fof(f763,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f132,f232,f137,f141,f81])).

fof(f141,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl7_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f137,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f232,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f230])).

fof(f981,plain,
    ( spl7_46
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f765,f230,f140,f135,f130,f978])).

fof(f765,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f132,f232,f137,f141,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f976,plain,
    ( ~ spl7_45
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f764,f230,f140,f135,f130,f973])).

fof(f764,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6
    | ~ spl7_11 ),
    inference(unit_resulting_resolution,[],[f132,f232,f137,f141,f84])).

fof(f760,plain,
    ( ~ spl7_6
    | ~ spl7_15
    | spl7_33 ),
    inference(avatar_split_clause,[],[f758,f743,f296,f140])).

fof(f743,plain,
    ( spl7_33
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f758,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ spl7_15
    | spl7_33 ),
    inference(subsumption_resolution,[],[f753,f744])).

fof(f744,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | spl7_33 ),
    inference(avatar_component_clause,[],[f743])).

fof(f753,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0)
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f75,f298])).

fof(f75,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( v1_subset_1(sK1,u1_struct_0(sK0))
      | ~ v3_tex_2(sK1,sK0) )
    & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK0))
            | ~ v3_tex_2(X1,sK0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( v1_subset_1(X1,u1_struct_0(sK0))
          | ~ v3_tex_2(X1,sK0) )
        & ( ~ v1_subset_1(X1,u1_struct_0(sK0))
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( v1_subset_1(sK1,u1_struct_0(sK0))
        | ~ v3_tex_2(sK1,sK0) )
      & ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f752,plain,
    ( ~ spl7_28
    | ~ spl7_33 ),
    inference(avatar_contradiction_clause,[],[f751])).

fof(f751,plain,
    ( $false
    | ~ spl7_28
    | ~ spl7_33 ),
    inference(subsumption_resolution,[],[f748,f687])).

fof(f748,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_33 ),
    inference(resolution,[],[f745,f112])).

fof(f112,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f745,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f743])).

fof(f717,plain,
    ( u1_struct_0(sK0) != sK1
    | r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f716,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_23
    | spl7_25 ),
    inference(avatar_split_clause,[],[f673,f543,f449,f283,f140,f135,f130,f125,f120,f115,f296])).

fof(f115,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f120,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f125,plain,
    ( spl7_3
  <=> v1_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f283,plain,
    ( spl7_13
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f449,plain,
    ( spl7_23
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f543,plain,
    ( spl7_25
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f673,plain,
    ( u1_struct_0(sK0) = sK1
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13
    | spl7_23
    | spl7_25 ),
    inference(subsumption_resolution,[],[f470,f672])).

fof(f672,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_23
    | spl7_25 ),
    inference(forward_demodulation,[],[f661,f666])).

fof(f666,plain,
    ( u1_struct_0(sK0) = sK4(u1_struct_0(sK0))
    | spl7_23
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f451,f545,f212])).

fof(f212,plain,(
    ! [X2] :
      ( v1_zfmisc_1(X2)
      | sK4(X2) = X2
      | v1_xboole_0(X2) ) ),
    inference(subsumption_resolution,[],[f209,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK4(X0),X0)
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( ~ v1_subset_1(sK4(X0),X0)
        & ~ v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK4(X0),X0)
        & ~ v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tex_2)).

fof(f209,plain,(
    ! [X2] :
      ( sK4(X2) = X2
      | v1_subset_1(sK4(X2),X2)
      | v1_zfmisc_1(X2)
      | v1_xboole_0(X2) ) ),
    inference(resolution,[],[f103,f90])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f545,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f543])).

fof(f451,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f449])).

fof(f661,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_23
    | spl7_25 ),
    inference(unit_resulting_resolution,[],[f451,f545,f90])).

fof(f470,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = sK1
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(resolution,[],[f309,f285])).

fof(f285,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f283])).

fof(f309,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f308,f225])).

fof(f225,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f224,f117])).

fof(f117,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f223,f122])).

fof(f122,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f120])).

fof(f223,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v2_tex_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f221,f132])).

fof(f221,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | v2_tex_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f88,f127])).

fof(f127,plain,
    ( v1_tdlat_3(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f308,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f307,f132])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f304,f137])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f142,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f142,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f715,plain,
    ( ~ spl7_32
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f373,f368,f157,f130,f120,f115,f712])).

fof(f373,plain,
    ( ~ v3_tex_2(sK3(sK0),sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f159,f370,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f710,plain,
    ( spl7_31
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f372,f368,f130,f125,f120,f115,f707])).

fof(f372,plain,
    ( v2_tex_2(sK3(sK0),sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f370,f88])).

fof(f688,plain,
    ( spl7_28
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f293,f289,f685])).

fof(f289,plain,
    ( spl7_14
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f293,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl7_14 ),
    inference(unit_resulting_resolution,[],[f291,f109])).

fof(f291,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f289])).

fof(f683,plain,
    ( spl7_27
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f277,f201,f157,f680])).

fof(f201,plain,
    ( spl7_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f277,plain,
    ( m1_subset_1(k1_xboole_0,sK3(sK0))
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f159,f203,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f203,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f546,plain,
    ( ~ spl7_25
    | ~ spl7_5
    | ~ spl7_7
    | spl7_16 ),
    inference(avatar_split_clause,[],[f323,f311,f144,f135,f543])).

fof(f144,plain,
    ( spl7_7
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f323,plain,
    ( ~ v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl7_5
    | ~ spl7_7
    | spl7_16 ),
    inference(unit_resulting_resolution,[],[f145,f137,f313,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_subset_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f94,f87])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f145,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f452,plain,
    ( ~ spl7_23
    | ~ spl7_5
    | spl7_16 ),
    inference(avatar_split_clause,[],[f318,f311,f135,f449])).

fof(f318,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_5
    | spl7_16 ),
    inference(unit_resulting_resolution,[],[f137,f313,f87])).

fof(f420,plain,
    ( spl7_7
    | spl7_15
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f207,f135,f296,f144])).

fof(f207,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(resolution,[],[f103,f137])).

fof(f394,plain,
    ( ~ spl7_22
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f267,f201,f130,f120,f115,f391])).

fof(f267,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f78,f203,f89])).

fof(f371,plain,
    ( spl7_21
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f179,f130,f368])).

fof(f179,plain,
    ( m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).

fof(f314,plain,
    ( ~ spl7_16
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f302,f140,f135,f130,f120,f115,f311])).

fof(f302,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f117,f122,f132,f137,f142,f89])).

fof(f292,plain,
    ( spl7_14
    | ~ spl7_5
    | spl7_7
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f287,f283,f144,f135,f289])).

fof(f287,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl7_5
    | spl7_7
    | ~ spl7_13 ),
    inference(forward_demodulation,[],[f285,f205])).

fof(f205,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl7_5
    | spl7_7 ),
    inference(unit_resulting_resolution,[],[f146,f137,f103])).

fof(f146,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl7_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f286,plain,
    ( spl7_13
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f165,f135,f283])).

fof(f165,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f137,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f261,plain,
    ( spl7_12
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f219,f130,f125,f120,f115,f258])).

fof(f219,plain,
    ( v2_tex_2(k1_xboole_0,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f78,f88])).

fof(f233,plain,
    ( spl7_11
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f218,f135,f130,f125,f120,f115,f230])).

fof(f218,plain,
    ( v2_tex_2(sK1,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f137,f88])).

fof(f204,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f183,f201])).

fof(f183,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f96,f78,f87])).

fof(f96,plain,(
    ! [X0] : v1_xboole_0(sK5(X0)) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_xboole_0(sK5(X0))
      & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f5,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK5(X0))
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f160,plain,
    ( spl7_9
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f155,f130,f157])).

fof(f155,plain,
    ( v1_xboole_0(sK3(sK0))
    | ~ spl7_4 ),
    inference(unit_resulting_resolution,[],[f132,f86])).

fof(f86,plain,(
    ! [X0] :
      ( v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f154,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f76,f151])).

fof(f76,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f149,plain,
    ( ~ spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f148,f144,f140])).

fof(f148,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl7_7 ),
    inference(subsumption_resolution,[],[f75,f146])).

fof(f147,plain,
    ( spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f74,f144,f140])).

fof(f74,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f138,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f73,f135])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f133,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f72,f130])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f128,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f71,f125])).

fof(f71,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f70,f120])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f118,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f69,f115])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:59:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.51  % (26809)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.51  % (26808)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.51  % (26804)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.51  % (26812)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.23/0.52  % (26817)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.52  % (26806)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.52  % (26819)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.53  % (26807)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.53  % (26825)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (26814)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.53  % (26822)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (26816)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.54  % (26804)Refutation not found, incomplete strategy% (26804)------------------------------
% 0.23/0.54  % (26804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.54  % (26824)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.54  % (26804)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.54  
% 0.23/0.54  % (26804)Memory used [KB]: 10874
% 0.23/0.54  % (26804)Time elapsed: 0.074 s
% 0.23/0.54  % (26804)------------------------------
% 0.23/0.54  % (26804)------------------------------
% 0.23/0.54  % (26823)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.54  % (26828)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.54  % (26820)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.54  % (26805)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.54  % (26810)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.54  % (26827)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.55  % (26813)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.55  % (26829)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.23/0.55  % (26815)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.56  % (26826)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.56  % (26821)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.56  % (26818)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.54/0.56  % (26811)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.54/0.57  % (26811)Refutation not found, incomplete strategy% (26811)------------------------------
% 1.54/0.57  % (26811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.57  % (26811)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.57  
% 1.54/0.57  % (26811)Memory used [KB]: 1791
% 1.54/0.57  % (26811)Time elapsed: 0.122 s
% 1.54/0.57  % (26811)------------------------------
% 1.54/0.57  % (26811)------------------------------
% 1.54/0.58  % (26810)Refutation not found, incomplete strategy% (26810)------------------------------
% 1.54/0.58  % (26810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (26810)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (26810)Memory used [KB]: 10874
% 1.54/0.58  % (26810)Time elapsed: 0.156 s
% 1.54/0.58  % (26810)------------------------------
% 1.54/0.58  % (26810)------------------------------
% 2.73/0.72  % (26813)Refutation not found, incomplete strategy% (26813)------------------------------
% 2.73/0.72  % (26813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.72  % (26813)Termination reason: Refutation not found, incomplete strategy
% 2.73/0.72  
% 2.73/0.72  % (26813)Memory used [KB]: 6268
% 2.73/0.72  % (26813)Time elapsed: 0.302 s
% 2.73/0.72  % (26813)------------------------------
% 2.73/0.72  % (26813)------------------------------
% 3.66/0.86  % (26827)Refutation found. Thanks to Tanya!
% 3.66/0.86  % SZS status Theorem for theBenchmark
% 3.66/0.86  % SZS output start Proof for theBenchmark
% 3.66/0.86  fof(f4215,plain,(
% 3.66/0.86    $false),
% 3.66/0.86    inference(avatar_sat_refutation,[],[f118,f123,f128,f133,f138,f147,f149,f154,f160,f204,f233,f261,f286,f292,f314,f371,f394,f420,f452,f546,f683,f688,f710,f715,f716,f717,f752,f760,f976,f981,f1023,f2326,f2997,f3315,f3669,f4141,f4193])).
% 3.66/0.86  fof(f4193,plain,(
% 3.66/0.86    spl7_16 | ~spl7_28 | spl7_45 | ~spl7_49 | ~spl7_107 | ~spl7_118),
% 3.66/0.86    inference(avatar_contradiction_clause,[],[f4192])).
% 3.66/0.86  fof(f4192,plain,(
% 3.66/0.86    $false | (spl7_16 | ~spl7_28 | spl7_45 | ~spl7_49 | ~spl7_107 | ~spl7_118)),
% 3.66/0.86    inference(subsumption_resolution,[],[f4164,f4170])).
% 3.66/0.86  fof(f4170,plain,(
% 3.66/0.86    r2_hidden(sK6(sK1,sK2(sK0,sK1),sK1),sK2(sK0,sK1)) | (spl7_16 | ~spl7_107 | ~spl7_118)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f313,f3668,f4140,f213])).
% 3.66/0.86  fof(f213,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X1)) | r2_hidden(X0,X1) | ~m1_subset_1(X0,X2) | v1_xboole_0(X2)) )),
% 3.66/0.86    inference(resolution,[],[f104,f97])).
% 3.66/0.86  fof(f97,plain,(
% 3.66/0.86    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f62])).
% 3.66/0.86  fof(f62,plain,(
% 3.66/0.86    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 3.66/0.86    inference(nnf_transformation,[],[f36])).
% 3.66/0.86  fof(f36,plain,(
% 3.66/0.86    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f2])).
% 3.66/0.86  fof(f2,axiom,(
% 3.66/0.86    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 3.66/0.86  fof(f104,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f40])).
% 3.66/0.86  fof(f40,plain,(
% 3.66/0.86    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f4])).
% 3.66/0.86  fof(f4,axiom,(
% 3.66/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 3.66/0.86  fof(f4140,plain,(
% 3.66/0.86    m1_subset_1(sK6(sK1,sK2(sK0,sK1),sK1),sK1) | ~spl7_118),
% 3.66/0.86    inference(avatar_component_clause,[],[f4138])).
% 3.66/0.86  fof(f4138,plain,(
% 3.66/0.86    spl7_118 <=> m1_subset_1(sK6(sK1,sK2(sK0,sK1),sK1),sK1)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_118])])).
% 3.66/0.86  fof(f3668,plain,(
% 3.66/0.86    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | ~spl7_107),
% 3.66/0.86    inference(avatar_component_clause,[],[f3666])).
% 3.66/0.86  fof(f3666,plain,(
% 3.66/0.86    spl7_107 <=> m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_107])])).
% 3.66/0.86  fof(f313,plain,(
% 3.66/0.86    ~v1_xboole_0(sK1) | spl7_16),
% 3.66/0.86    inference(avatar_component_clause,[],[f311])).
% 3.66/0.86  fof(f311,plain,(
% 3.66/0.86    spl7_16 <=> v1_xboole_0(sK1)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 3.66/0.86  fof(f4164,plain,(
% 3.66/0.86    ~r2_hidden(sK6(sK1,sK2(sK0,sK1),sK1),sK2(sK0,sK1)) | (spl7_16 | ~spl7_28 | spl7_45 | ~spl7_49 | ~spl7_118)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f313,f687,f975,f1022,f4140,f256])).
% 3.66/0.86  fof(f256,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X2,X0,X1),X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(sK6(X2,X0,X1),X1) | v1_xboole_0(X1)) )),
% 3.66/0.86    inference(resolution,[],[f107,f97])).
% 3.66/0.86  fof(f107,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f67])).
% 3.66/0.86  fof(f67,plain,(
% 3.66/0.86    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK6(X0,X1,X2),X2) | ~r2_hidden(sK6(X0,X1,X2),X1)) & (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1)) & m1_subset_1(sK6(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f65,f66])).
% 3.66/0.86  fof(f66,plain,(
% 3.66/0.86    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK6(X0,X1,X2),X2) | ~r2_hidden(sK6(X0,X1,X2),X1)) & (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1)) & m1_subset_1(sK6(X0,X1,X2),X0)))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f65,plain,(
% 3.66/0.86    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(flattening,[],[f64])).
% 3.66/0.86  fof(f64,plain,(
% 3.66/0.86    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(nnf_transformation,[],[f42])).
% 3.66/0.86  fof(f42,plain,(
% 3.66/0.86    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(flattening,[],[f41])).
% 3.66/0.86  fof(f41,plain,(
% 3.66/0.86    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f8])).
% 3.66/0.86  fof(f8,axiom,(
% 3.66/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 3.66/0.86  fof(f1022,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl7_49),
% 3.66/0.86    inference(avatar_component_clause,[],[f1020])).
% 3.66/0.86  fof(f1020,plain,(
% 3.66/0.86    spl7_49 <=> m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 3.66/0.86  fof(f975,plain,(
% 3.66/0.86    sK1 != sK2(sK0,sK1) | spl7_45),
% 3.66/0.86    inference(avatar_component_clause,[],[f973])).
% 3.66/0.86  fof(f973,plain,(
% 3.66/0.86    spl7_45 <=> sK1 = sK2(sK0,sK1)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 3.66/0.86  fof(f687,plain,(
% 3.66/0.86    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl7_28),
% 3.66/0.86    inference(avatar_component_clause,[],[f685])).
% 3.66/0.86  fof(f685,plain,(
% 3.66/0.86    spl7_28 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 3.66/0.86  fof(f4141,plain,(
% 3.66/0.86    spl7_118 | ~spl7_28 | spl7_45 | ~spl7_49),
% 3.66/0.86    inference(avatar_split_clause,[],[f1031,f1020,f973,f685,f4138])).
% 3.66/0.86  fof(f1031,plain,(
% 3.66/0.86    m1_subset_1(sK6(sK1,sK2(sK0,sK1),sK1),sK1) | (~spl7_28 | spl7_45 | ~spl7_49)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f687,f975,f1022,f105])).
% 3.66/0.86  fof(f105,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),X0) | X1 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f67])).
% 3.66/0.86  fof(f3669,plain,(
% 3.66/0.86    spl7_107 | ~spl7_46),
% 3.66/0.86    inference(avatar_split_clause,[],[f988,f978,f3666])).
% 3.66/0.86  fof(f978,plain,(
% 3.66/0.86    spl7_46 <=> r1_tarski(sK1,sK2(sK0,sK1))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 3.66/0.86  fof(f988,plain,(
% 3.66/0.86    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | ~spl7_46),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f980,f109])).
% 3.66/0.86  fof(f109,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f68])).
% 3.66/0.86  fof(f68,plain,(
% 3.66/0.86    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.66/0.86    inference(nnf_transformation,[],[f10])).
% 3.66/0.86  fof(f10,axiom,(
% 3.66/0.86    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.66/0.86  fof(f980,plain,(
% 3.66/0.86    r1_tarski(sK1,sK2(sK0,sK1)) | ~spl7_46),
% 3.66/0.86    inference(avatar_component_clause,[],[f978])).
% 3.66/0.86  fof(f3315,plain,(
% 3.66/0.86    ~spl7_9 | ~spl7_16 | spl7_89 | ~spl7_104),
% 3.66/0.86    inference(avatar_contradiction_clause,[],[f3314])).
% 3.66/0.86  fof(f3314,plain,(
% 3.66/0.86    $false | (~spl7_9 | ~spl7_16 | spl7_89 | ~spl7_104)),
% 3.66/0.86    inference(subsumption_resolution,[],[f3300,f2996])).
% 3.66/0.86  fof(f2996,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1)) | ~spl7_104),
% 3.66/0.86    inference(avatar_component_clause,[],[f2994])).
% 3.66/0.86  fof(f2994,plain,(
% 3.66/0.86    spl7_104 <=> m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_104])])).
% 3.66/0.86  fof(f3300,plain,(
% 3.66/0.86    ~m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1)) | (~spl7_9 | ~spl7_16 | spl7_89)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f2325,f312,f493])).
% 3.66/0.86  fof(f493,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~v1_xboole_0(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl7_9),
% 3.66/0.86    inference(condensation,[],[f489])).
% 3.66/0.86  fof(f489,plain,(
% 3.66/0.86    ( ! [X10,X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(X9)) | k1_xboole_0 = X8 | ~m1_subset_1(X8,k1_zfmisc_1(X10)) | ~v1_xboole_0(X10)) ) | ~spl7_9),
% 3.66/0.86    inference(resolution,[],[f251,f111])).
% 3.66/0.86  fof(f111,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f45])).
% 3.66/0.86  fof(f45,plain,(
% 3.66/0.86    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.66/0.86    inference(ennf_transformation,[],[f12])).
% 3.66/0.86  fof(f12,axiom,(
% 3.66/0.86    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 3.66/0.86  fof(f251,plain,(
% 3.66/0.86    ( ! [X0,X1] : (r2_hidden(sK6(X0,k1_xboole_0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1) ) | ~spl7_9),
% 3.66/0.86    inference(subsumption_resolution,[],[f243,f196])).
% 3.66/0.86  fof(f196,plain,(
% 3.66/0.86    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl7_9),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f159,f78,f111])).
% 3.66/0.86  fof(f78,plain,(
% 3.66/0.86    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f6])).
% 3.66/0.86  fof(f6,axiom,(
% 3.66/0.86    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.66/0.86  fof(f159,plain,(
% 3.66/0.86    v1_xboole_0(sK3(sK0)) | ~spl7_9),
% 3.66/0.86    inference(avatar_component_clause,[],[f157])).
% 3.66/0.86  fof(f157,plain,(
% 3.66/0.86    spl7_9 <=> v1_xboole_0(sK3(sK0))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 3.66/0.86  fof(f243,plain,(
% 3.66/0.86    ( ! [X0,X1] : (r2_hidden(sK6(X0,k1_xboole_0,X1),X1) | r2_hidden(sK6(X0,k1_xboole_0,X1),k1_xboole_0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1) )),
% 3.66/0.86    inference(resolution,[],[f106,f78])).
% 3.66/0.86  fof(f106,plain,(
% 3.66/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 3.66/0.86    inference(cnf_transformation,[],[f67])).
% 3.66/0.86  fof(f312,plain,(
% 3.66/0.86    v1_xboole_0(sK1) | ~spl7_16),
% 3.66/0.86    inference(avatar_component_clause,[],[f311])).
% 3.66/0.86  fof(f2325,plain,(
% 3.66/0.86    k1_xboole_0 != sK2(sK0,k1_xboole_0) | spl7_89),
% 3.66/0.86    inference(avatar_component_clause,[],[f2323])).
% 3.66/0.86  fof(f2323,plain,(
% 3.66/0.86    spl7_89 <=> k1_xboole_0 = sK2(sK0,k1_xboole_0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_89])])).
% 3.66/0.86  fof(f2997,plain,(
% 3.66/0.86    spl7_104 | ~spl7_4 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_21 | ~spl7_27 | ~spl7_31 | spl7_32),
% 3.66/0.86    inference(avatar_split_clause,[],[f827,f712,f707,f680,f368,f296,f157,f151,f130,f2994])).
% 3.66/0.86  fof(f130,plain,(
% 3.66/0.86    spl7_4 <=> l1_pre_topc(sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 3.66/0.86  fof(f151,plain,(
% 3.66/0.86    spl7_8 <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 3.66/0.86  fof(f296,plain,(
% 3.66/0.86    spl7_15 <=> u1_struct_0(sK0) = sK1),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 3.66/0.86  fof(f368,plain,(
% 3.66/0.86    spl7_21 <=> m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 3.66/0.86  fof(f680,plain,(
% 3.66/0.86    spl7_27 <=> m1_subset_1(k1_xboole_0,sK3(sK0))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 3.66/0.86  fof(f707,plain,(
% 3.66/0.86    spl7_31 <=> v2_tex_2(sK3(sK0),sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 3.66/0.86  fof(f712,plain,(
% 3.66/0.86    spl7_32 <=> v3_tex_2(sK3(sK0),sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 3.66/0.86  fof(f827,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,k1_xboole_0),k1_zfmisc_1(sK1)) | (~spl7_4 | ~spl7_8 | ~spl7_9 | ~spl7_15 | ~spl7_21 | ~spl7_27 | ~spl7_31 | spl7_32)),
% 3.66/0.86    inference(forward_demodulation,[],[f826,f776])).
% 3.66/0.86  fof(f776,plain,(
% 3.66/0.86    k1_xboole_0 = sK3(sK0) | (~spl7_8 | ~spl7_9 | ~spl7_27)),
% 3.66/0.86    inference(subsumption_resolution,[],[f775,f182])).
% 3.66/0.86  fof(f182,plain,(
% 3.66/0.86    ( ! [X0] : (~m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(sK3(sK0)))) ) | ~spl7_9),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f77,f159,f87])).
% 3.66/0.86  fof(f87,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f27])).
% 3.66/0.86  fof(f27,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.66/0.86    inference(ennf_transformation,[],[f9])).
% 3.66/0.86  fof(f9,axiom,(
% 3.66/0.86    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 3.66/0.86  fof(f77,plain,(
% 3.66/0.86    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f3])).
% 3.66/0.86  fof(f3,axiom,(
% 3.66/0.86    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 3.66/0.86  fof(f775,plain,(
% 3.66/0.86    k1_xboole_0 = sK3(sK0) | m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK3(sK0))) | (~spl7_8 | ~spl7_27)),
% 3.66/0.86    inference(resolution,[],[f682,f217])).
% 3.66/0.86  fof(f217,plain,(
% 3.66/0.86    ( ! [X0] : (~m1_subset_1(k1_xboole_0,X0) | k1_xboole_0 = X0 | m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X0))) ) | ~spl7_8),
% 3.66/0.86    inference(superposition,[],[f101,f153])).
% 3.66/0.86  fof(f153,plain,(
% 3.66/0.86    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) | ~spl7_8),
% 3.66/0.86    inference(avatar_component_clause,[],[f151])).
% 3.66/0.86  fof(f101,plain,(
% 3.66/0.86    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f38])).
% 3.66/0.86  fof(f38,plain,(
% 3.66/0.86    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 3.66/0.86    inference(flattening,[],[f37])).
% 3.66/0.86  fof(f37,plain,(
% 3.66/0.86    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 3.66/0.86    inference(ennf_transformation,[],[f7])).
% 3.66/0.86  fof(f7,axiom,(
% 3.66/0.86    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).
% 3.66/0.86  fof(f682,plain,(
% 3.66/0.86    m1_subset_1(k1_xboole_0,sK3(sK0)) | ~spl7_27),
% 3.66/0.86    inference(avatar_component_clause,[],[f680])).
% 3.66/0.86  fof(f826,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,sK3(sK0)),k1_zfmisc_1(sK1)) | (~spl7_4 | ~spl7_15 | ~spl7_21 | ~spl7_31 | spl7_32)),
% 3.66/0.86    inference(forward_demodulation,[],[f819,f298])).
% 3.66/0.86  fof(f298,plain,(
% 3.66/0.86    u1_struct_0(sK0) = sK1 | ~spl7_15),
% 3.66/0.86    inference(avatar_component_clause,[],[f296])).
% 3.66/0.86  fof(f819,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,sK3(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_4 | ~spl7_21 | ~spl7_31 | spl7_32)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f709,f370,f714,f81])).
% 3.66/0.86  fof(f81,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f55])).
% 3.66/0.86  fof(f55,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f53,f54])).
% 3.66/0.86  fof(f54,plain,(
% 3.66/0.86    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f53,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(rectify,[],[f52])).
% 3.66/0.86  fof(f52,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(flattening,[],[f51])).
% 3.66/0.86  fof(f51,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(nnf_transformation,[],[f25])).
% 3.66/0.86  fof(f25,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(flattening,[],[f24])).
% 3.66/0.86  fof(f24,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(ennf_transformation,[],[f16])).
% 3.66/0.86  fof(f16,axiom,(
% 3.66/0.86    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 3.66/0.86  fof(f714,plain,(
% 3.66/0.86    ~v3_tex_2(sK3(sK0),sK0) | spl7_32),
% 3.66/0.86    inference(avatar_component_clause,[],[f712])).
% 3.66/0.86  fof(f370,plain,(
% 3.66/0.86    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_21),
% 3.66/0.86    inference(avatar_component_clause,[],[f368])).
% 3.66/0.86  fof(f709,plain,(
% 3.66/0.86    v2_tex_2(sK3(sK0),sK0) | ~spl7_31),
% 3.66/0.86    inference(avatar_component_clause,[],[f707])).
% 3.66/0.86  fof(f132,plain,(
% 3.66/0.86    l1_pre_topc(sK0) | ~spl7_4),
% 3.66/0.86    inference(avatar_component_clause,[],[f130])).
% 3.66/0.86  fof(f2326,plain,(
% 3.66/0.86    ~spl7_89 | ~spl7_4 | ~spl7_12 | spl7_22),
% 3.66/0.86    inference(avatar_split_clause,[],[f620,f391,f258,f130,f2323])).
% 3.66/0.86  fof(f258,plain,(
% 3.66/0.86    spl7_12 <=> v2_tex_2(k1_xboole_0,sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 3.66/0.86  fof(f391,plain,(
% 3.66/0.86    spl7_22 <=> v3_tex_2(k1_xboole_0,sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 3.66/0.86  fof(f620,plain,(
% 3.66/0.86    k1_xboole_0 != sK2(sK0,k1_xboole_0) | (~spl7_4 | ~spl7_12 | spl7_22)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f260,f78,f393,f84])).
% 3.66/0.86  fof(f84,plain,(
% 3.66/0.86    ( ! [X0,X1] : (sK2(X0,X1) != X1 | v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f55])).
% 3.66/0.86  fof(f393,plain,(
% 3.66/0.86    ~v3_tex_2(k1_xboole_0,sK0) | spl7_22),
% 3.66/0.86    inference(avatar_component_clause,[],[f391])).
% 3.66/0.86  fof(f260,plain,(
% 3.66/0.86    v2_tex_2(k1_xboole_0,sK0) | ~spl7_12),
% 3.66/0.86    inference(avatar_component_clause,[],[f258])).
% 3.66/0.86  fof(f1023,plain,(
% 3.66/0.86    spl7_49 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_15),
% 3.66/0.86    inference(avatar_split_clause,[],[f767,f296,f230,f140,f135,f130,f1020])).
% 3.66/0.86  fof(f135,plain,(
% 3.66/0.86    spl7_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 3.66/0.86  fof(f140,plain,(
% 3.66/0.86    spl7_6 <=> v3_tex_2(sK1,sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 3.66/0.86  fof(f230,plain,(
% 3.66/0.86    spl7_11 <=> v2_tex_2(sK1,sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 3.66/0.86  fof(f767,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | (~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11 | ~spl7_15)),
% 3.66/0.86    inference(forward_demodulation,[],[f763,f298])).
% 3.66/0.86  fof(f763,plain,(
% 3.66/0.86    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f232,f137,f141,f81])).
% 3.66/0.86  fof(f141,plain,(
% 3.66/0.86    ~v3_tex_2(sK1,sK0) | spl7_6),
% 3.66/0.86    inference(avatar_component_clause,[],[f140])).
% 3.66/0.86  fof(f137,plain,(
% 3.66/0.86    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 3.66/0.86    inference(avatar_component_clause,[],[f135])).
% 3.66/0.86  fof(f232,plain,(
% 3.66/0.86    v2_tex_2(sK1,sK0) | ~spl7_11),
% 3.66/0.86    inference(avatar_component_clause,[],[f230])).
% 3.66/0.86  fof(f981,plain,(
% 3.66/0.86    spl7_46 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11),
% 3.66/0.86    inference(avatar_split_clause,[],[f765,f230,f140,f135,f130,f978])).
% 3.66/0.86  fof(f765,plain,(
% 3.66/0.86    r1_tarski(sK1,sK2(sK0,sK1)) | (~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f232,f137,f141,f83])).
% 3.66/0.86  fof(f83,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_tarski(X1,sK2(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f55])).
% 3.66/0.86  fof(f976,plain,(
% 3.66/0.86    ~spl7_45 | ~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11),
% 3.66/0.86    inference(avatar_split_clause,[],[f764,f230,f140,f135,f130,f973])).
% 3.66/0.86  fof(f764,plain,(
% 3.66/0.86    sK1 != sK2(sK0,sK1) | (~spl7_4 | ~spl7_5 | spl7_6 | ~spl7_11)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f232,f137,f141,f84])).
% 3.66/0.86  fof(f760,plain,(
% 3.66/0.86    ~spl7_6 | ~spl7_15 | spl7_33),
% 3.66/0.86    inference(avatar_split_clause,[],[f758,f743,f296,f140])).
% 3.66/0.86  fof(f743,plain,(
% 3.66/0.86    spl7_33 <=> v1_subset_1(sK1,sK1)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 3.66/0.86  fof(f758,plain,(
% 3.66/0.86    ~v3_tex_2(sK1,sK0) | (~spl7_15 | spl7_33)),
% 3.66/0.86    inference(subsumption_resolution,[],[f753,f744])).
% 3.66/0.86  fof(f744,plain,(
% 3.66/0.86    ~v1_subset_1(sK1,sK1) | spl7_33),
% 3.66/0.86    inference(avatar_component_clause,[],[f743])).
% 3.66/0.86  fof(f753,plain,(
% 3.66/0.86    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0) | ~spl7_15),
% 3.66/0.86    inference(forward_demodulation,[],[f75,f298])).
% 3.66/0.86  fof(f75,plain,(
% 3.66/0.86    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  fof(f50,plain,(
% 3.66/0.86    ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.66/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 3.66/0.86  fof(f48,plain,(
% 3.66/0.86    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f49,plain,(
% 3.66/0.86    ? [X1] : ((v1_subset_1(X1,u1_struct_0(sK0)) | ~v3_tex_2(X1,sK0)) & (~v1_subset_1(X1,u1_struct_0(sK0)) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)) & (~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f47,plain,(
% 3.66/0.86    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.66/0.86    inference(flattening,[],[f46])).
% 3.66/0.86  fof(f46,plain,(
% 3.66/0.86    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.66/0.86    inference(nnf_transformation,[],[f23])).
% 3.66/0.86  fof(f23,plain,(
% 3.66/0.86    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.66/0.86    inference(flattening,[],[f22])).
% 3.66/0.86  fof(f22,plain,(
% 3.66/0.86    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f21])).
% 3.66/0.86  fof(f21,negated_conjecture,(
% 3.66/0.86    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.66/0.86    inference(negated_conjecture,[],[f20])).
% 3.66/0.86  fof(f20,conjecture,(
% 3.66/0.86    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 3.66/0.86  fof(f752,plain,(
% 3.66/0.86    ~spl7_28 | ~spl7_33),
% 3.66/0.86    inference(avatar_contradiction_clause,[],[f751])).
% 3.66/0.86  fof(f751,plain,(
% 3.66/0.86    $false | (~spl7_28 | ~spl7_33)),
% 3.66/0.86    inference(subsumption_resolution,[],[f748,f687])).
% 3.66/0.86  fof(f748,plain,(
% 3.66/0.86    ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl7_33),
% 3.66/0.86    inference(resolution,[],[f745,f112])).
% 3.66/0.86  fof(f112,plain,(
% 3.66/0.86    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 3.66/0.86    inference(equality_resolution,[],[f102])).
% 3.66/0.86  fof(f102,plain,(
% 3.66/0.86    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f63])).
% 3.66/0.86  fof(f63,plain,(
% 3.66/0.86    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(nnf_transformation,[],[f39])).
% 3.66/0.86  fof(f39,plain,(
% 3.66/0.86    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f15])).
% 3.66/0.86  fof(f15,axiom,(
% 3.66/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 3.66/0.86  fof(f745,plain,(
% 3.66/0.86    v1_subset_1(sK1,sK1) | ~spl7_33),
% 3.66/0.86    inference(avatar_component_clause,[],[f743])).
% 3.66/0.86  fof(f717,plain,(
% 3.66/0.86    u1_struct_0(sK0) != sK1 | r1_tarski(sK1,sK1) | ~r1_tarski(sK1,u1_struct_0(sK0))),
% 3.66/0.86    introduced(theory_tautology_sat_conflict,[])).
% 3.66/0.86  fof(f716,plain,(
% 3.66/0.86    spl7_15 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_23 | spl7_25),
% 3.66/0.86    inference(avatar_split_clause,[],[f673,f543,f449,f283,f140,f135,f130,f125,f120,f115,f296])).
% 3.66/0.86  fof(f115,plain,(
% 3.66/0.86    spl7_1 <=> v2_struct_0(sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 3.66/0.86  fof(f120,plain,(
% 3.66/0.86    spl7_2 <=> v2_pre_topc(sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 3.66/0.86  fof(f125,plain,(
% 3.66/0.86    spl7_3 <=> v1_tdlat_3(sK0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 3.66/0.86  fof(f283,plain,(
% 3.66/0.86    spl7_13 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 3.66/0.86  fof(f449,plain,(
% 3.66/0.86    spl7_23 <=> v1_xboole_0(u1_struct_0(sK0))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 3.66/0.86  fof(f543,plain,(
% 3.66/0.86    spl7_25 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 3.66/0.86  fof(f673,plain,(
% 3.66/0.86    u1_struct_0(sK0) = sK1 | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13 | spl7_23 | spl7_25)),
% 3.66/0.86    inference(subsumption_resolution,[],[f470,f672])).
% 3.66/0.86  fof(f672,plain,(
% 3.66/0.86    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_23 | spl7_25)),
% 3.66/0.86    inference(forward_demodulation,[],[f661,f666])).
% 3.66/0.86  fof(f666,plain,(
% 3.66/0.86    u1_struct_0(sK0) = sK4(u1_struct_0(sK0)) | (spl7_23 | spl7_25)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f451,f545,f212])).
% 3.66/0.86  fof(f212,plain,(
% 3.66/0.86    ( ! [X2] : (v1_zfmisc_1(X2) | sK4(X2) = X2 | v1_xboole_0(X2)) )),
% 3.66/0.86    inference(subsumption_resolution,[],[f209,f93])).
% 3.66/0.86  fof(f93,plain,(
% 3.66/0.86    ( ! [X0] : (~v1_subset_1(sK4(X0),X0) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f59])).
% 3.66/0.86  fof(f59,plain,(
% 3.66/0.86    ! [X0] : ((~v1_subset_1(sK4(X0),X0) & ~v1_zfmisc_1(sK4(X0)) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.66/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f33,f58])).
% 3.66/0.86  fof(f58,plain,(
% 3.66/0.86    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK4(X0),X0) & ~v1_zfmisc_1(sK4(X0)) & ~v1_xboole_0(sK4(X0)) & m1_subset_1(sK4(X0),k1_zfmisc_1(X0))))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f33,plain,(
% 3.66/0.86    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.66/0.86    inference(flattening,[],[f32])).
% 3.66/0.86  fof(f32,plain,(
% 3.66/0.86    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f17])).
% 3.66/0.86  fof(f17,axiom,(
% 3.66/0.86    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ? [X1] : (~v1_subset_1(X1,X0) & ~v1_zfmisc_1(X1) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tex_2)).
% 3.66/0.86  fof(f209,plain,(
% 3.66/0.86    ( ! [X2] : (sK4(X2) = X2 | v1_subset_1(sK4(X2),X2) | v1_zfmisc_1(X2) | v1_xboole_0(X2)) )),
% 3.66/0.86    inference(resolution,[],[f103,f90])).
% 3.66/0.86  fof(f90,plain,(
% 3.66/0.86    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f59])).
% 3.66/0.86  fof(f103,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f63])).
% 3.66/0.86  fof(f545,plain,(
% 3.66/0.86    ~v1_zfmisc_1(u1_struct_0(sK0)) | spl7_25),
% 3.66/0.86    inference(avatar_component_clause,[],[f543])).
% 3.66/0.86  fof(f451,plain,(
% 3.66/0.86    ~v1_xboole_0(u1_struct_0(sK0)) | spl7_23),
% 3.66/0.86    inference(avatar_component_clause,[],[f449])).
% 3.66/0.86  fof(f661,plain,(
% 3.66/0.86    m1_subset_1(sK4(u1_struct_0(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_23 | spl7_25)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f451,f545,f90])).
% 3.66/0.86  fof(f470,plain,(
% 3.66/0.86    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK1 | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_13)),
% 3.66/0.86    inference(resolution,[],[f309,f285])).
% 3.66/0.86  fof(f285,plain,(
% 3.66/0.86    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl7_13),
% 3.66/0.86    inference(avatar_component_clause,[],[f283])).
% 3.66/0.86  fof(f309,plain,(
% 3.66/0.86    ( ! [X0] : (~r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 3.66/0.86    inference(subsumption_resolution,[],[f308,f225])).
% 3.66/0.86  fof(f225,plain,(
% 3.66/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 3.66/0.86    inference(subsumption_resolution,[],[f224,f117])).
% 3.66/0.86  fof(f117,plain,(
% 3.66/0.86    ~v2_struct_0(sK0) | spl7_1),
% 3.66/0.86    inference(avatar_component_clause,[],[f115])).
% 3.66/0.86  fof(f224,plain,(
% 3.66/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | v2_struct_0(sK0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 3.66/0.86    inference(subsumption_resolution,[],[f223,f122])).
% 3.66/0.86  fof(f122,plain,(
% 3.66/0.86    v2_pre_topc(sK0) | ~spl7_2),
% 3.66/0.86    inference(avatar_component_clause,[],[f120])).
% 3.66/0.86  fof(f223,plain,(
% 3.66/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | (~spl7_3 | ~spl7_4)),
% 3.66/0.86    inference(subsumption_resolution,[],[f221,f132])).
% 3.66/0.86  fof(f221,plain,(
% 3.66/0.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tex_2(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 3.66/0.86    inference(resolution,[],[f88,f127])).
% 3.66/0.86  fof(f127,plain,(
% 3.66/0.86    v1_tdlat_3(sK0) | ~spl7_3),
% 3.66/0.86    inference(avatar_component_clause,[],[f125])).
% 3.66/0.86  fof(f88,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~v1_tdlat_3(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f29])).
% 3.66/0.86  fof(f29,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.86    inference(flattening,[],[f28])).
% 3.66/0.86  fof(f28,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f18])).
% 3.66/0.86  fof(f18,axiom,(
% 3.66/0.86    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 3.66/0.86  fof(f308,plain,(
% 3.66/0.86    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | (~spl7_4 | ~spl7_5 | ~spl7_6)),
% 3.66/0.86    inference(subsumption_resolution,[],[f307,f132])).
% 3.66/0.86  fof(f307,plain,(
% 3.66/0.86    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~l1_pre_topc(sK0)) ) | (~spl7_5 | ~spl7_6)),
% 3.66/0.86    inference(subsumption_resolution,[],[f304,f137])).
% 3.66/0.86  fof(f304,plain,(
% 3.66/0.86    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl7_6),
% 3.66/0.86    inference(resolution,[],[f142,f80])).
% 3.66/0.86  fof(f80,plain,(
% 3.66/0.86    ( ! [X0,X3,X1] : (~v3_tex_2(X1,X0) | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | X1 = X3 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f55])).
% 3.66/0.86  fof(f142,plain,(
% 3.66/0.86    v3_tex_2(sK1,sK0) | ~spl7_6),
% 3.66/0.86    inference(avatar_component_clause,[],[f140])).
% 3.66/0.86  fof(f715,plain,(
% 3.66/0.86    ~spl7_32 | spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_9 | ~spl7_21),
% 3.66/0.86    inference(avatar_split_clause,[],[f373,f368,f157,f130,f120,f115,f712])).
% 3.66/0.86  fof(f373,plain,(
% 3.66/0.86    ~v3_tex_2(sK3(sK0),sK0) | (spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_9 | ~spl7_21)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f117,f122,f132,f159,f370,f89])).
% 3.66/0.86  fof(f89,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f31])).
% 3.66/0.86  fof(f31,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.66/0.86    inference(flattening,[],[f30])).
% 3.66/0.86  fof(f30,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f19])).
% 3.66/0.86  fof(f19,axiom,(
% 3.66/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 3.66/0.86  fof(f710,plain,(
% 3.66/0.86    spl7_31 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_21),
% 3.66/0.86    inference(avatar_split_clause,[],[f372,f368,f130,f125,f120,f115,f707])).
% 3.66/0.86  fof(f372,plain,(
% 3.66/0.86    v2_tex_2(sK3(sK0),sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_21)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f370,f88])).
% 3.66/0.86  fof(f688,plain,(
% 3.66/0.86    spl7_28 | ~spl7_14),
% 3.66/0.86    inference(avatar_split_clause,[],[f293,f289,f685])).
% 3.66/0.86  fof(f289,plain,(
% 3.66/0.86    spl7_14 <=> r1_tarski(sK1,sK1)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 3.66/0.86  fof(f293,plain,(
% 3.66/0.86    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl7_14),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f291,f109])).
% 3.66/0.86  fof(f291,plain,(
% 3.66/0.86    r1_tarski(sK1,sK1) | ~spl7_14),
% 3.66/0.86    inference(avatar_component_clause,[],[f289])).
% 3.66/0.86  fof(f683,plain,(
% 3.66/0.86    spl7_27 | ~spl7_9 | ~spl7_10),
% 3.66/0.86    inference(avatar_split_clause,[],[f277,f201,f157,f680])).
% 3.66/0.86  fof(f201,plain,(
% 3.66/0.86    spl7_10 <=> v1_xboole_0(k1_xboole_0)),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 3.66/0.86  fof(f277,plain,(
% 3.66/0.86    m1_subset_1(k1_xboole_0,sK3(sK0)) | (~spl7_9 | ~spl7_10)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f159,f203,f100])).
% 3.66/0.86  fof(f100,plain,(
% 3.66/0.86    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f62])).
% 3.66/0.86  fof(f203,plain,(
% 3.66/0.86    v1_xboole_0(k1_xboole_0) | ~spl7_10),
% 3.66/0.86    inference(avatar_component_clause,[],[f201])).
% 3.66/0.86  fof(f546,plain,(
% 3.66/0.86    ~spl7_25 | ~spl7_5 | ~spl7_7 | spl7_16),
% 3.66/0.86    inference(avatar_split_clause,[],[f323,f311,f144,f135,f543])).
% 3.66/0.86  fof(f144,plain,(
% 3.66/0.86    spl7_7 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 3.66/0.86    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 3.66/0.86  fof(f323,plain,(
% 3.66/0.86    ~v1_zfmisc_1(u1_struct_0(sK0)) | (~spl7_5 | ~spl7_7 | spl7_16)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f145,f137,f313,f113])).
% 3.66/0.86  fof(f113,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_subset_1(X1,X0)) )),
% 3.66/0.86    inference(subsumption_resolution,[],[f94,f87])).
% 3.66/0.86  fof(f94,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f35])).
% 3.66/0.86  fof(f35,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 3.66/0.86    inference(flattening,[],[f34])).
% 3.66/0.86  fof(f34,plain,(
% 3.66/0.86    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 3.66/0.86    inference(ennf_transformation,[],[f14])).
% 3.66/0.86  fof(f14,axiom,(
% 3.66/0.86    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).
% 3.66/0.86  fof(f145,plain,(
% 3.66/0.86    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_7),
% 3.66/0.86    inference(avatar_component_clause,[],[f144])).
% 3.66/0.86  fof(f452,plain,(
% 3.66/0.86    ~spl7_23 | ~spl7_5 | spl7_16),
% 3.66/0.86    inference(avatar_split_clause,[],[f318,f311,f135,f449])).
% 3.66/0.86  fof(f318,plain,(
% 3.66/0.86    ~v1_xboole_0(u1_struct_0(sK0)) | (~spl7_5 | spl7_16)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f137,f313,f87])).
% 3.66/0.86  fof(f420,plain,(
% 3.66/0.86    spl7_7 | spl7_15 | ~spl7_5),
% 3.66/0.86    inference(avatar_split_clause,[],[f207,f135,f296,f144])).
% 3.66/0.86  fof(f207,plain,(
% 3.66/0.86    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_5),
% 3.66/0.86    inference(resolution,[],[f103,f137])).
% 3.66/0.86  fof(f394,plain,(
% 3.66/0.86    ~spl7_22 | spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_10),
% 3.66/0.86    inference(avatar_split_clause,[],[f267,f201,f130,f120,f115,f391])).
% 3.66/0.86  fof(f267,plain,(
% 3.66/0.86    ~v3_tex_2(k1_xboole_0,sK0) | (spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_10)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f117,f122,f132,f78,f203,f89])).
% 3.66/0.86  fof(f371,plain,(
% 3.66/0.86    spl7_21 | ~spl7_4),
% 3.66/0.86    inference(avatar_split_clause,[],[f179,f130,f368])).
% 3.66/0.86  fof(f179,plain,(
% 3.66/0.86    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_4),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f85])).
% 3.66/0.86  fof(f85,plain,(
% 3.66/0.86    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f57])).
% 3.66/0.86  fof(f57,plain,(
% 3.66/0.86    ! [X0] : ((v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f56])).
% 3.66/0.86  fof(f56,plain,(
% 3.66/0.86    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f26,plain,(
% 3.66/0.86    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.66/0.86    inference(ennf_transformation,[],[f13])).
% 3.66/0.86  fof(f13,axiom,(
% 3.66/0.86    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_connsp_1)).
% 3.66/0.86  fof(f314,plain,(
% 3.66/0.86    ~spl7_16 | spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6),
% 3.66/0.86    inference(avatar_split_clause,[],[f302,f140,f135,f130,f120,f115,f311])).
% 3.66/0.86  fof(f302,plain,(
% 3.66/0.86    ~v1_xboole_0(sK1) | (spl7_1 | ~spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_6)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f117,f122,f132,f137,f142,f89])).
% 3.66/0.86  fof(f292,plain,(
% 3.66/0.86    spl7_14 | ~spl7_5 | spl7_7 | ~spl7_13),
% 3.66/0.86    inference(avatar_split_clause,[],[f287,f283,f144,f135,f289])).
% 3.66/0.86  fof(f287,plain,(
% 3.66/0.86    r1_tarski(sK1,sK1) | (~spl7_5 | spl7_7 | ~spl7_13)),
% 3.66/0.86    inference(forward_demodulation,[],[f285,f205])).
% 3.66/0.86  fof(f205,plain,(
% 3.66/0.86    u1_struct_0(sK0) = sK1 | (~spl7_5 | spl7_7)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f146,f137,f103])).
% 3.66/0.86  fof(f146,plain,(
% 3.66/0.86    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl7_7),
% 3.66/0.86    inference(avatar_component_clause,[],[f144])).
% 3.66/0.86  fof(f286,plain,(
% 3.66/0.86    spl7_13 | ~spl7_5),
% 3.66/0.86    inference(avatar_split_clause,[],[f165,f135,f283])).
% 3.66/0.86  fof(f165,plain,(
% 3.66/0.86    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl7_5),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f137,f108])).
% 3.66/0.86  fof(f108,plain,(
% 3.66/0.86    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f68])).
% 3.66/0.86  fof(f261,plain,(
% 3.66/0.86    spl7_12 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4),
% 3.66/0.86    inference(avatar_split_clause,[],[f219,f130,f125,f120,f115,f258])).
% 3.66/0.86  fof(f219,plain,(
% 3.66/0.86    v2_tex_2(k1_xboole_0,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f78,f88])).
% 3.66/0.86  fof(f233,plain,(
% 3.66/0.86    spl7_11 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 3.66/0.86    inference(avatar_split_clause,[],[f218,f135,f130,f125,f120,f115,f230])).
% 3.66/0.86  fof(f218,plain,(
% 3.66/0.86    v2_tex_2(sK1,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f117,f122,f127,f132,f137,f88])).
% 3.66/0.86  fof(f204,plain,(
% 3.66/0.86    spl7_10),
% 3.66/0.86    inference(avatar_split_clause,[],[f183,f201])).
% 3.66/0.86  fof(f183,plain,(
% 3.66/0.86    v1_xboole_0(k1_xboole_0)),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f96,f78,f87])).
% 3.66/0.86  fof(f96,plain,(
% 3.66/0.86    ( ! [X0] : (v1_xboole_0(sK5(X0))) )),
% 3.66/0.86    inference(cnf_transformation,[],[f61])).
% 3.66/0.86  fof(f61,plain,(
% 3.66/0.86    ! [X0] : (v1_xboole_0(sK5(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)))),
% 3.66/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f5,f60])).
% 3.66/0.86  fof(f60,plain,(
% 3.66/0.86    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK5(X0)) & m1_subset_1(sK5(X0),k1_zfmisc_1(X0))))),
% 3.66/0.86    introduced(choice_axiom,[])).
% 3.66/0.86  fof(f5,axiom,(
% 3.66/0.86    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc2_subset_1)).
% 3.66/0.86  fof(f160,plain,(
% 3.66/0.86    spl7_9 | ~spl7_4),
% 3.66/0.86    inference(avatar_split_clause,[],[f155,f130,f157])).
% 3.66/0.86  fof(f155,plain,(
% 3.66/0.86    v1_xboole_0(sK3(sK0)) | ~spl7_4),
% 3.66/0.86    inference(unit_resulting_resolution,[],[f132,f86])).
% 3.66/0.86  fof(f86,plain,(
% 3.66/0.86    ( ! [X0] : (v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0)) )),
% 3.66/0.86    inference(cnf_transformation,[],[f57])).
% 3.66/0.86  fof(f154,plain,(
% 3.66/0.86    spl7_8),
% 3.66/0.86    inference(avatar_split_clause,[],[f76,f151])).
% 3.66/0.86  fof(f76,plain,(
% 3.66/0.86    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 3.66/0.86    inference(cnf_transformation,[],[f1])).
% 3.66/0.86  fof(f1,axiom,(
% 3.66/0.86    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 3.66/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 3.66/0.86  fof(f149,plain,(
% 3.66/0.86    ~spl7_6 | spl7_7),
% 3.66/0.86    inference(avatar_split_clause,[],[f148,f144,f140])).
% 3.66/0.86  fof(f148,plain,(
% 3.66/0.86    ~v3_tex_2(sK1,sK0) | spl7_7),
% 3.66/0.86    inference(subsumption_resolution,[],[f75,f146])).
% 3.66/0.86  fof(f147,plain,(
% 3.66/0.86    spl7_6 | ~spl7_7),
% 3.66/0.86    inference(avatar_split_clause,[],[f74,f144,f140])).
% 3.66/0.86  fof(f74,plain,(
% 3.66/0.86    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  fof(f138,plain,(
% 3.66/0.86    spl7_5),
% 3.66/0.86    inference(avatar_split_clause,[],[f73,f135])).
% 3.66/0.86  fof(f73,plain,(
% 3.66/0.86    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  fof(f133,plain,(
% 3.66/0.86    spl7_4),
% 3.66/0.86    inference(avatar_split_clause,[],[f72,f130])).
% 3.66/0.86  fof(f72,plain,(
% 3.66/0.86    l1_pre_topc(sK0)),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  fof(f128,plain,(
% 3.66/0.86    spl7_3),
% 3.66/0.86    inference(avatar_split_clause,[],[f71,f125])).
% 3.66/0.86  fof(f71,plain,(
% 3.66/0.86    v1_tdlat_3(sK0)),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  fof(f123,plain,(
% 3.66/0.86    spl7_2),
% 3.66/0.86    inference(avatar_split_clause,[],[f70,f120])).
% 3.66/0.86  fof(f70,plain,(
% 3.66/0.86    v2_pre_topc(sK0)),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  fof(f118,plain,(
% 3.66/0.86    ~spl7_1),
% 3.66/0.86    inference(avatar_split_clause,[],[f69,f115])).
% 3.66/0.86  fof(f69,plain,(
% 3.66/0.86    ~v2_struct_0(sK0)),
% 3.66/0.86    inference(cnf_transformation,[],[f50])).
% 3.66/0.86  % SZS output end Proof for theBenchmark
% 3.66/0.86  % (26827)------------------------------
% 3.66/0.86  % (26827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.66/0.86  % (26827)Termination reason: Refutation
% 3.66/0.86  
% 3.66/0.86  % (26827)Memory used [KB]: 13304
% 3.66/0.86  % (26827)Time elapsed: 0.412 s
% 3.66/0.86  % (26827)------------------------------
% 3.66/0.86  % (26827)------------------------------
% 3.66/0.86  % (26803)Success in time 0.494 s
%------------------------------------------------------------------------------
