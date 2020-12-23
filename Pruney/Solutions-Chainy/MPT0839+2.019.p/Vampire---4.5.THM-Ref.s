%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 263 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   11
%              Number of atoms          :  285 ( 705 expanded)
%              Number of equality atoms :   35 ( 118 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f628,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f156,f379,f455,f570,f572,f575,f577,f584,f627])).

fof(f627,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | spl5_13 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | spl5_13 ),
    inference(resolution,[],[f618,f595])).

fof(f595,plain,
    ( ~ r2_hidden(sK3(k1_xboole_0),sK1)
    | ~ spl5_2
    | spl5_13 ),
    inference(backward_demodulation,[],[f247,f592])).

fof(f592,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f589,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f589,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f76,f116])).

fof(f116,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f76,plain,
    ( v1_xboole_0(k1_relset_1(sK1,sK0,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_2
  <=> v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f247,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | spl5_13 ),
    inference(resolution,[],[f240,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f240,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl5_13
  <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f618,plain,
    ( r2_hidden(sK3(k1_xboole_0),sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f114,f592])).

fof(f114,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_6
  <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f584,plain,
    ( spl5_5
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f581,f239,f110])).

fof(f110,plain,
    ( spl5_5
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f581,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(resolution,[],[f152,f48])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f152,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relat_1(sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(backward_demodulation,[],[f39,f116])).

fof(f39,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f577,plain,
    ( spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f576,f113,f110])).

fof(f576,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(global_subsumption,[],[f83,f488])).

fof(f488,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2)) ),
    inference(superposition,[],[f103,f102])).

fof(f102,plain,(
    sK2 = k7_relat_1(sK2,sK1) ),
    inference(global_subsumption,[],[f83,f101])).

fof(f101,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK1) ),
    inference(resolution,[],[f52,f86])).

fof(f86,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f60,f40])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(k1_relat_1(k7_relat_1(X0,X1))),X1)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(k1_relat_1(k7_relat_1(X0,X1))) ) ),
    inference(resolution,[],[f54,f48])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f575,plain,(
    spl5_35 ),
    inference(avatar_contradiction_clause,[],[f574])).

fof(f574,plain,
    ( $false
    | spl5_35 ),
    inference(resolution,[],[f566,f81])).

fof(f81,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f45,f44])).

fof(f44,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f566,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f565])).

fof(f565,plain,
    ( spl5_35
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f572,plain,(
    spl5_36 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | spl5_36 ),
    inference(resolution,[],[f569,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f65])).

fof(f65,plain,(
    k1_xboole_0 = sK4 ),
    inference(resolution,[],[f46,f63])).

fof(f63,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f569,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_36 ),
    inference(avatar_component_clause,[],[f568])).

fof(f568,plain,
    ( spl5_36
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f570,plain,
    ( ~ spl5_35
    | ~ spl5_36
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f563,f377,f568,f565])).

fof(f377,plain,
    ( spl5_18
  <=> ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f563,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl5_18 ),
    inference(superposition,[],[f378,f179])).

fof(f179,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f78,f66])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f378,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_zfmisc_1(X0,sK0))
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f377])).

fof(f455,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f453])).

fof(f453,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl5_4 ),
    inference(superposition,[],[f418,f176])).

fof(f176,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f68,f66])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f47,f46])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f418,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl5_4 ),
    inference(backward_demodulation,[],[f157,f408])).

fof(f408,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f385,f46])).

fof(f385,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_4 ),
    inference(resolution,[],[f98,f48])).

fof(f98,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_4
  <=> ! [X0] : ~ r2_hidden(X0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f157,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f41,f120])).

fof(f120,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f40])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f379,plain,
    ( spl5_4
    | spl5_18
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f375,f110,f377,f97])).

fof(f375,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r2_hidden(X1,sK2)
        | ~ v1_xboole_0(k2_zfmisc_1(X0,sK0)) )
    | ~ spl5_5 ),
    inference(forward_demodulation,[],[f363,f278])).

fof(f278,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f111,f46])).

fof(f111,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f110])).

fof(f363,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ r2_hidden(X1,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(X0,sK0)) ) ),
    inference(resolution,[],[f146,f40])).

fof(f146,plain,(
    ! [X19,X17,X20,X18,X16] :
      ( ~ r1_tarski(k1_relat_1(X16),X17)
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X18,X19)))
      | ~ r2_hidden(X20,X16)
      | ~ v1_xboole_0(k2_zfmisc_1(X17,X19)) ) ),
    inference(resolution,[],[f62,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

fof(f156,plain,
    ( spl5_1
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | spl5_1
    | ~ spl5_6 ),
    inference(resolution,[],[f150,f114])).

fof(f150,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | spl5_1 ),
    inference(backward_demodulation,[],[f79,f116])).

fof(f79,plain,
    ( ~ r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)
    | spl5_1 ),
    inference(resolution,[],[f51,f73])).

fof(f73,plain,
    ( ~ m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl5_1
  <=> m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f69,f75,f72])).

fof(f69,plain,
    ( v1_xboole_0(k1_relset_1(sK1,sK0,sK2))
    | ~ m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) ),
    inference(resolution,[],[f48,f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:01:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (29143)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.44  % (29143)Refutation not found, incomplete strategy% (29143)------------------------------
% 0.21/0.44  % (29143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29143)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.44  
% 0.21/0.44  % (29143)Memory used [KB]: 6140
% 0.21/0.44  % (29143)Time elapsed: 0.026 s
% 0.21/0.44  % (29143)------------------------------
% 0.21/0.44  % (29143)------------------------------
% 0.21/0.47  % (29151)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.48  % (29141)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.48  % (29137)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (29140)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (29146)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (29138)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (29144)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.49  % (29158)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.49  % (29159)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.49  % (29144)Refutation not found, incomplete strategy% (29144)------------------------------
% 0.21/0.49  % (29144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (29144)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (29144)Memory used [KB]: 10618
% 0.21/0.49  % (29144)Time elapsed: 0.086 s
% 0.21/0.49  % (29144)------------------------------
% 0.21/0.49  % (29144)------------------------------
% 0.21/0.50  % (29139)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (29157)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (29148)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (29139)Refutation not found, incomplete strategy% (29139)------------------------------
% 0.21/0.50  % (29139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29139)Memory used [KB]: 10618
% 0.21/0.50  % (29139)Time elapsed: 0.085 s
% 0.21/0.50  % (29139)------------------------------
% 0.21/0.50  % (29139)------------------------------
% 0.21/0.50  % (29154)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.50  % (29153)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (29147)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (29156)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (29156)Refutation not found, incomplete strategy% (29156)------------------------------
% 0.21/0.50  % (29156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (29156)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (29156)Memory used [KB]: 6140
% 0.21/0.50  % (29156)Time elapsed: 0.102 s
% 0.21/0.50  % (29156)------------------------------
% 0.21/0.50  % (29156)------------------------------
% 0.21/0.51  % (29136)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (29146)Refutation not found, incomplete strategy% (29146)------------------------------
% 0.21/0.51  % (29146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29146)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29146)Memory used [KB]: 10618
% 0.21/0.51  % (29146)Time elapsed: 0.103 s
% 0.21/0.51  % (29146)------------------------------
% 0.21/0.51  % (29146)------------------------------
% 0.21/0.51  % (29159)Refutation not found, incomplete strategy% (29159)------------------------------
% 0.21/0.51  % (29159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29159)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29159)Memory used [KB]: 10618
% 0.21/0.51  % (29159)Time elapsed: 0.089 s
% 0.21/0.51  % (29159)------------------------------
% 0.21/0.51  % (29159)------------------------------
% 0.21/0.51  % (29150)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.52  % (29148)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f628,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f77,f156,f379,f455,f570,f572,f575,f577,f584,f627])).
% 0.21/0.52  fof(f627,plain,(
% 0.21/0.52    ~spl5_2 | ~spl5_6 | spl5_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f619])).
% 0.21/0.52  fof(f619,plain,(
% 0.21/0.52    $false | (~spl5_2 | ~spl5_6 | spl5_13)),
% 0.21/0.52    inference(resolution,[],[f618,f595])).
% 0.21/0.52  fof(f595,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k1_xboole_0),sK1) | (~spl5_2 | spl5_13)),
% 0.21/0.52    inference(backward_demodulation,[],[f247,f592])).
% 0.21/0.52  fof(f592,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_2),
% 0.21/0.52    inference(resolution,[],[f589,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.52  fof(f589,plain,(
% 0.21/0.52    v1_xboole_0(k1_relat_1(sK2)) | ~spl5_2),
% 0.21/0.52    inference(backward_demodulation,[],[f76,f116])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f58,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f18])).
% 0.21/0.52  fof(f18,conjecture,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) | ~spl5_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    spl5_2 <=> v1_xboole_0(k1_relset_1(sK1,sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k1_relat_1(sK2)),sK1) | spl5_13),
% 0.21/0.52    inference(resolution,[],[f240,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f239])).
% 0.21/0.52  fof(f239,plain,(
% 0.21/0.52    spl5_13 <=> m1_subset_1(sK3(k1_relat_1(sK2)),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f618,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_xboole_0),sK1) | (~spl5_2 | ~spl5_6)),
% 0.21/0.52    inference(forward_demodulation,[],[f114,f592])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_relat_1(sK2)),sK1) | ~spl5_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl5_6 <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.52  fof(f584,plain,(
% 0.21/0.52    spl5_5 | ~spl5_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f581,f239,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl5_5 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.52  fof(f581,plain,(
% 0.21/0.52    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.52    inference(resolution,[],[f152,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k1_relat_1(sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.52    inference(backward_demodulation,[],[f39,f116])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f577,plain,(
% 0.21/0.52    spl5_5 | spl5_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f576,f113,f110])).
% 0.21/0.52  fof(f576,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_relat_1(sK2)),sK1) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.52    inference(global_subsumption,[],[f83,f488])).
% 0.21/0.52  fof(f488,plain,(
% 0.21/0.52    r2_hidden(sK3(k1_relat_1(sK2)),sK1) | ~v1_relat_1(sK2) | v1_xboole_0(k1_relat_1(sK2))),
% 0.21/0.52    inference(superposition,[],[f103,f102])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    sK2 = k7_relat_1(sK2,sK1)),
% 0.21/0.52    inference(global_subsumption,[],[f83,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f52,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    v4_relat_1(sK2,sK1)),
% 0.21/0.52    inference(resolution,[],[f60,f40])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK3(k1_relat_1(k7_relat_1(X0,X1))),X1) | ~v1_relat_1(X0) | v1_xboole_0(k1_relat_1(k7_relat_1(X0,X1)))) )),
% 0.21/0.52    inference(resolution,[],[f54,f48])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    v1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f57,f40])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f575,plain,(
% 0.21/0.52    spl5_35),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f574])).
% 0.21/0.52  fof(f574,plain,(
% 0.21/0.52    $false | spl5_35),
% 0.21/0.52    inference(resolution,[],[f566,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f53,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(forward_demodulation,[],[f45,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.52    inference(unused_predicate_definition_removal,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f566,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl5_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f565])).
% 0.21/0.52  fof(f565,plain,(
% 0.21/0.52    spl5_35 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.52  fof(f572,plain,(
% 0.21/0.52    spl5_36),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f571])).
% 0.21/0.52  fof(f571,plain,(
% 0.21/0.52    $false | spl5_36),
% 0.21/0.52    inference(resolution,[],[f569,f66])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    inference(backward_demodulation,[],[f63,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    k1_xboole_0 = sK4),
% 0.21/0.52    inference(resolution,[],[f46,f63])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    v1_xboole_0(sK4)),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ? [X0] : v1_xboole_0(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).
% 0.21/0.52  fof(f569,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | spl5_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f568])).
% 0.21/0.52  fof(f568,plain,(
% 0.21/0.52    spl5_36 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.52  fof(f570,plain,(
% 0.21/0.52    ~spl5_35 | ~spl5_36 | ~spl5_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f563,f377,f568,f565])).
% 0.21/0.52  fof(f377,plain,(
% 0.21/0.52    spl5_18 <=> ! [X0] : (~r1_tarski(k1_xboole_0,X0) | ~v1_xboole_0(k2_zfmisc_1(X0,sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.21/0.52  fof(f563,plain,(
% 0.21/0.52    ~v1_xboole_0(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k1_xboole_0) | ~spl5_18),
% 0.21/0.52    inference(superposition,[],[f378,f179])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(resolution,[],[f78,f66])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f50,f46])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(k2_zfmisc_1(X0,sK0)) | ~r1_tarski(k1_xboole_0,X0)) ) | ~spl5_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f377])).
% 0.21/0.52  fof(f455,plain,(
% 0.21/0.52    ~spl5_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f454])).
% 0.21/0.52  fof(f454,plain,(
% 0.21/0.52    $false | ~spl5_4),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f453])).
% 0.21/0.52  fof(f453,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | ~spl5_4),
% 0.21/0.52    inference(superposition,[],[f418,f176])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f68,f66])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f47,f46])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.21/0.52  fof(f418,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~spl5_4),
% 0.21/0.52    inference(backward_demodulation,[],[f157,f408])).
% 0.21/0.52  fof(f408,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f385,f46])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    v1_xboole_0(sK2) | ~spl5_4),
% 0.21/0.52    inference(resolution,[],[f98,f48])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl5_4 <=> ! [X0] : ~r2_hidden(X0,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relat_1(sK2)),
% 0.21/0.52    inference(superposition,[],[f41,f120])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f59,f40])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    spl5_4 | spl5_18 | ~spl5_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f375,f110,f377,f97])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(X0,sK0))) ) | ~spl5_5),
% 0.21/0.52    inference(forward_demodulation,[],[f363,f278])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_5),
% 0.21/0.52    inference(resolution,[],[f111,f46])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    v1_xboole_0(k1_relat_1(sK2)) | ~spl5_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f110])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(sK2),X0) | ~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(X0,sK0))) )),
% 0.21/0.52    inference(resolution,[],[f146,f40])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ( ! [X19,X17,X20,X18,X16] : (~r1_tarski(k1_relat_1(X16),X17) | ~m1_subset_1(X16,k1_zfmisc_1(k2_zfmisc_1(X18,X19))) | ~r2_hidden(X20,X16) | ~v1_xboole_0(k2_zfmisc_1(X17,X19))) )),
% 0.21/0.52    inference(resolution,[],[f62,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.52    inference(flattening,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl5_1 | ~spl5_6),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f155])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    $false | (spl5_1 | ~spl5_6)),
% 0.21/0.52    inference(resolution,[],[f150,f114])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k1_relat_1(sK2)),sK1) | spl5_1),
% 0.21/0.52    inference(backward_demodulation,[],[f79,f116])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ~r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) | spl5_1),
% 0.21/0.52    inference(resolution,[],[f51,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ~m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    spl5_1 <=> m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ~spl5_1 | spl5_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f69,f75,f72])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)),
% 0.21/0.52    inference(resolution,[],[f48,f39])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (29148)------------------------------
% 0.21/0.52  % (29148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29148)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (29148)Memory used [KB]: 11129
% 0.21/0.52  % (29148)Time elapsed: 0.102 s
% 0.21/0.52  % (29148)------------------------------
% 0.21/0.52  % (29148)------------------------------
% 0.21/0.52  % (29135)Success in time 0.162 s
%------------------------------------------------------------------------------
