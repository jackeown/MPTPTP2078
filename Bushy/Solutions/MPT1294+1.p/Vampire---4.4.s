%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t10_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   50 (  93 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :  120 ( 242 expanded)
%              Number of equality atoms :   46 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f125,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f64,f68,f73,f77,f91,f95,f123])).

fof(f123,plain,
    ( spl3_5
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f121,f80])).

fof(f80,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_10
  <=> k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f121,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f118,f67])).

fof(f67,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_5
  <=> k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f118,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_14 ),
    inference(resolution,[],[f94,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k1_xboole_0 != k7_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k7_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',t46_setfam_1)).

fof(f94,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_14
  <=> m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f95,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f83,f71,f93])).

fof(f71,plain,
    ( spl3_6
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f83,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',dt_k7_setfam_1)).

fof(f72,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f91,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f75,f62,f79])).

fof(f62,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f75,plain,
    ( spl3_8
  <=> k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f76,f63])).

fof(f63,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f76,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f77,plain,
    ( spl3_8
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f54,f51,f75])).

fof(f51,plain,
    ( spl3_0
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f54,plain,
    ( k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = sK1
    | ~ spl3_0 ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',involutiveness_k7_setfam_1)).

fof(f52,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f51])).

fof(f73,plain,
    ( spl3_6
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f69,f62,f51,f71])).

fof(f69,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_0
    | ~ spl3_2 ),
    inference(superposition,[],[f52,f63])).

fof(f68,plain,
    ( ~ spl3_5
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f59,f51,f66])).

fof(f59,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl3_0 ),
    inference(subsumption_resolution,[],[f49,f58])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_0 ),
    inference(subsumption_resolution,[],[f56,f34])).

fof(f34,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_2__t10_tops_2.p',t10_tops_2)).

fof(f56,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | ~ spl3_0 ),
    inference(resolution,[],[f52,f37])).

fof(f49,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f64,plain,
    ( spl3_2
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f58,f51,f62])).

fof(f53,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f36,f51])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
