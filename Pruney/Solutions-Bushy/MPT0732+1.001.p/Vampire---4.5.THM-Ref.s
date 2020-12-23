%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0732+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  73 expanded)
%              Number of leaves         :    9 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 244 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f49])).

fof(f49,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r2_hidden(sK1,sK2)
    & r2_hidden(sK0,sK1)
    & v1_ordinal1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1)
        & v1_ordinal1(X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r2_hidden(sK1,sK2)
      & r2_hidden(sK0,sK1)
      & v1_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r2_hidden(X1,X2)
      & r2_hidden(X0,X1)
      & v1_ordinal1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_ordinal1(X2)
       => ( ( r2_hidden(X1,X2)
            & r2_hidden(X0,X1) )
         => r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( v1_ordinal1(X2)
     => ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X1) )
       => r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_ordinal1)).

fof(f38,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> ! [X2] : ~ r2_hidden(X2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f44,f22])).

fof(f22,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f43,f23])).

fof(f43,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(sK0,X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f41,f24])).

fof(f24,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f41,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,sK2)
        | ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(X1,X0) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X1,sK2)
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f35,f40,f37])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X1,sK2)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(resolution,[],[f34,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f26,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,sK2)
      | ~ r2_hidden(X1,sK2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f33,f21])).

fof(f21,plain,(
    v1_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_ordinal1(X2)
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

%------------------------------------------------------------------------------
