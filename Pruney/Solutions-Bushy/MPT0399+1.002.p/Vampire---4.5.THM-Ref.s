%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0399+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 138 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  181 ( 302 expanded)
%              Number of equality atoms :   24 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f38,f42,f47,f52,f62,f69,f95,f103,f104,f105,f107])).

fof(f107,plain,(
    ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl3_10 ),
    inference(resolution,[],[f87,f27])).

fof(f27,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(sK1(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f87,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_10
  <=> ! [X0] : ~ m1_subset_1(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f105,plain,
    ( spl3_10
    | spl3_11
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f83,f67,f50,f40,f89,f86])).

fof(f89,plain,
    ( spl3_11
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f40,plain,
    ( spl3_3
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f50,plain,
    ( spl3_5
  <=> r1_setfam_1(sK0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f67,plain,
    ( spl3_8
  <=> o_0_0_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK0)
        | ~ m1_subset_1(X0,sK0) )
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(resolution,[],[f82,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f82,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(resolution,[],[f71,f51])).

fof(f51,plain,
    ( r1_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ r1_setfam_1(X1,o_0_0_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_3
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f70,f68])).

fof(f68,plain,
    ( o_0_0_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_setfam_1(X1,sK1(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl3_3 ),
    inference(resolution,[],[f29,f54])).

fof(f54,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f53,f27])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X1),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(sK2(X1),X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f21])).

fof(f21,plain,(
    ! [X1] :
      ( ? [X3] : r2_hidden(X3,X1)
     => r2_hidden(sK2(X1),X1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] : r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] : ~ r2_hidden(X3,X1)
            & r2_hidden(X2,X0) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f104,plain,
    ( o_0_0_xboole_0 != sK0
    | o_0_0_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f103,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f99,f89,f45,f101])).

fof(f101,plain,
    ( spl3_12
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f45,plain,
    ( spl3_4
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f99,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f98,f46])).

fof(f46,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f98,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_11 ),
    inference(resolution,[],[f90,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f90,plain,
    ( v1_xboole_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f89])).

fof(f95,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | ~ spl3_6 ),
    inference(resolution,[],[f58,f27])).

fof(f58,plain,
    ( ! [X0] : ~ m1_subset_1(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X0] : ~ m1_subset_1(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f69,plain,
    ( spl3_8
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f65,f60,f45,f67])).

fof(f60,plain,
    ( spl3_7
  <=> v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f65,plain,
    ( o_0_0_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f64,f46])).

fof(f64,plain,
    ( k1_xboole_0 = sK1(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl3_7 ),
    inference(resolution,[],[f61,f26])).

fof(f61,plain,
    ( v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl3_6
    | spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f40,f60,f57])).

fof(f55,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK1(k1_zfmisc_1(o_0_0_xboole_0)))
        | ~ m1_subset_1(X0,sK1(k1_zfmisc_1(o_0_0_xboole_0))) )
    | ~ spl3_3 ),
    inference(resolution,[],[f54,f28])).

fof(f52,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f48,f45,f36,f50])).

fof(f36,plain,
    ( spl3_2
  <=> r1_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,
    ( r1_setfam_1(sK0,o_0_0_xboole_0)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f37,f46])).

fof(f37,plain,
    ( r1_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f47,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f43,f40,f45])).

fof(f43,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl3_3 ),
    inference(resolution,[],[f26,f41])).

fof(f42,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f40])).

fof(f25,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f23,f36])).

fof(f23,plain,(
    r1_setfam_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != sK0
    & r1_setfam_1(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_setfam_1(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_setfam_1(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_setfam_1(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( r1_setfam_1(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( r1_setfam_1(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

fof(f34,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f24,f32])).

fof(f32,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f24,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

%------------------------------------------------------------------------------
