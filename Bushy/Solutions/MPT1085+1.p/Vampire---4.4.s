%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : finset_1__t13_finset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:12 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of leaves         :   14 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   94 ( 160 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f107,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f68,f75,f82,f89,f102,f106])).

fof(f106,plain,
    ( ~ spl3_0
    | spl3_3
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f105])).

fof(f105,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f104,f67])).

fof(f67,plain,
    ( ~ v1_finset_1(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_3
  <=> ~ v1_finset_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f104,plain,
    ( v1_finset_1(sK0)
    | ~ spl3_0
    | ~ spl3_6 ),
    inference(resolution,[],[f94,f81])).

fof(f81,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | v1_finset_1(X0) )
    | ~ spl3_0 ),
    inference(resolution,[],[f92,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',t3_subset)).

fof(f92,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
        | v1_finset_1(X0) )
    | ~ spl3_0 ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,
    ( v1_finset_1(sK1)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl3_0
  <=> v1_finset_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_finset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_finset_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_finset_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_finset_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_finset_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_finset_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',cc2_finset_1)).

fof(f102,plain,
    ( spl3_10
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f93,f59,f100])).

fof(f100,plain,
    ( spl3_10
  <=> v1_finset_1(sK2(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f93,plain,
    ( v1_finset_1(sK2(k1_zfmisc_1(sK1)))
    | ~ spl3_0 ),
    inference(resolution,[],[f92,f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',existence_m1_subset_1)).

fof(f89,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f87,plain,
    ( spl3_8
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f42,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',d2_xboole_0)).

fof(f82,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f38,f80])).

fof(f38,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ v1_finset_1(sK0)
    & v1_finset_1(sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34])).

fof(f34,plain,
    ( ? [X0,X1] :
        ( ~ v1_finset_1(X0)
        & v1_finset_1(X1)
        & r1_tarski(X0,X1) )
   => ( ~ v1_finset_1(sK0)
      & v1_finset_1(sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ~ v1_finset_1(X0)
      & v1_finset_1(X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_finset_1(X1)
          & r1_tarski(X0,X1) )
       => v1_finset_1(X0) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_finset_1(X1)
        & r1_tarski(X0,X1) )
     => v1_finset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',t13_finset_1)).

fof(f75,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f73])).

fof(f73,plain,
    ( spl3_4
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f41,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/finset_1__t13_finset_1.p',dt_o_0_0_xboole_0)).

fof(f68,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f66])).

fof(f40,plain,(
    ~ v1_finset_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f61,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f39,f59])).

fof(f39,plain,(
    v1_finset_1(sK1) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
