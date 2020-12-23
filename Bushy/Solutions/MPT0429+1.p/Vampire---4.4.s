%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : setfam_1__t61_setfam_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:19 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  51 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 (  90 expanded)
%              Number of equality atoms :    3 (   5 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f111,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f71,f78,f89,f110])).

fof(f110,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl2_7 ),
    inference(resolution,[],[f100,f88])).

fof(f88,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_7
  <=> ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f100,plain,(
    ! [X0] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',t37_zfmisc_1)).

fof(f98,plain,(
    ! [X0] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f93,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',t2_xboole_1)).

fof(f93,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,X1)
      | r2_hidden(X2,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f92,f42])).

fof(f42,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',fc1_subset_1)).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_xboole_0(k1_zfmisc_1(X1))
      | r2_hidden(X2,k1_zfmisc_1(X1))
      | ~ r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f48,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',t3_subset)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',t2_subset)).

fof(f89,plain,
    ( ~ spl2_7
    | spl2_5 ),
    inference(avatar_split_clause,[],[f81,f76,f87])).

fof(f76,plain,
    ( spl2_5
  <=> ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f81,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f52,f77])).

fof(f77,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f33])).

fof(f33,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',t61_setfam_1)).

fof(f71,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f41,f69])).

fof(f69,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',d2_xboole_0)).

fof(f64,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f57,f62])).

fof(f62,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f40,f41])).

fof(f40,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/setfam_1__t61_setfam_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
