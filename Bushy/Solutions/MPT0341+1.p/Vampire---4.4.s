%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : subset_1__t4_subset_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:24 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  36 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f47,f54,f56])).

fof(f56,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f53,f33])).

fof(f33,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f28,f27])).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t4_subset_1.p',d3_subset_1)).

fof(f28,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t4_subset_1.p',dt_k1_subset_1)).

fof(f53,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_5
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f54,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f20])).

fof(f20,plain,
    ( ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
   => ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t4_subset_1.p',t4_subset_1)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f26,f45])).

fof(f45,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f26,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t4_subset_1.p',d2_xboole_0)).

fof(f40,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f32,f38])).

fof(f38,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f32,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f25,f26])).

fof(f25,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/subset_1__t4_subset_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
