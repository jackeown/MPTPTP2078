%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t1_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:36 EDT 2019

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 169 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f78,f85,f92,f101,f109,f116,f121])).

fof(f121,plain,
    ( ~ spl4_6
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f118,f108])).

fof(f108,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl4_11
  <=> ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f118,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(resolution,[],[f57,f91])).

fof(f91,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t1_tops_2.p',t3_subset)).

fof(f116,plain,
    ( spl4_12
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f94,f76,f114])).

fof(f114,plain,
    ( spl4_12
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f76,plain,
    ( spl4_2
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f94,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl4_2 ),
    inference(resolution,[],[f51,f77])).

fof(f77,plain,
    ( l1_struct_0(sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t1_tops_2.p',d3_struct_0)).

fof(f109,plain,
    ( ~ spl4_11
    | spl4_5
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f102,f99,f83,f107])).

fof(f83,plain,
    ( spl4_5
  <=> ~ r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f99,plain,
    ( spl4_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f102,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5
    | ~ spl4_8 ),
    inference(superposition,[],[f84,f100])).

fof(f100,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f84,plain,
    ( ~ r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f101,plain,
    ( spl4_8
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f93,f69,f99])).

fof(f69,plain,
    ( spl4_0
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f93,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl4_0 ),
    inference(resolution,[],[f51,f70])).

fof(f70,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f69])).

fof(f92,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f46,f90])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f24,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(sK0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(X0)))
        & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X1,k9_setfam_1(k2_struct_0(X0)))
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => r1_tarski(X1,k9_setfam_1(k2_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t1_tops_2.p',t1_tops_2)).

fof(f85,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f63,f83])).

fof(f63,plain,(
    ~ r1_tarski(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f47,f48])).

fof(f48,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t1_tops_2.p',redefinition_k9_setfam_1)).

fof(f47,plain,(
    ~ r1_tarski(sK1,k9_setfam_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f62,f76])).

fof(f62,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    l1_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f43])).

fof(f43,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK3) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t1_tops_2.p',existence_l1_struct_0)).

fof(f71,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f45,f69])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
