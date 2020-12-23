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
% DateTime   : Thu Dec  3 13:02:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 249 expanded)
%              Number of leaves         :   30 (  85 expanded)
%              Depth                    :   10
%              Number of atoms          :  401 ( 921 expanded)
%              Number of equality atoms :   43 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f512,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f90,f96,f100,f102,f118,f129,f148,f150,f159,f161,f207,f251,f271,f286,f477,f511])).

fof(f511,plain,
    ( spl3_2
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | spl3_2
    | ~ spl3_12
    | ~ spl3_14
    | ~ spl3_21 ),
    inference(resolution,[],[f496,f158])).

fof(f158,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl3_14
  <=> r1_tarski(k1_relat_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f496,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl3_2
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(resolution,[],[f495,f78])).

fof(f78,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f495,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f206,f147])).

fof(f147,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_12
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f206,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl3_21
  <=> ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f477,plain,
    ( ~ spl3_27
    | ~ spl3_31 ),
    inference(avatar_contradiction_clause,[],[f469])).

fof(f469,plain,
    ( $false
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(resolution,[],[f270,f247])).

fof(f247,plain,
    ( ! [X0] : ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl3_27
  <=> ! [X0] : ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f270,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_31
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f286,plain,
    ( ~ spl3_12
    | ~ spl3_14
    | spl3_28 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_14
    | spl3_28 ),
    inference(resolution,[],[f257,f158])).

fof(f257,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl3_12
    | spl3_28 ),
    inference(backward_demodulation,[],[f250,f147])).

fof(f250,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f249])).

fof(f249,plain,
    ( spl3_28
  <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f271,plain,
    ( ~ spl3_9
    | ~ spl3_3
    | spl3_31
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f267,f146,f127,f269,f80,f133])).

fof(f133,plain,
    ( spl3_9
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f80,plain,
    ( spl3_3
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f127,plain,
    ( spl3_8
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f267,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f259,f170])).

fof(f170,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f128,f169])).

fof(f169,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f167,f50])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f167,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f69,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f128,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f259,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_12 ),
    inference(superposition,[],[f54,f147])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f251,plain,
    ( spl3_27
    | ~ spl3_28
    | spl3_1 ),
    inference(avatar_split_clause,[],[f240,f74,f249,f246])).

fof(f74,plain,
    ( spl3_1
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | spl3_1 ),
    inference(resolution,[],[f72,f75])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f207,plain,
    ( ~ spl3_9
    | ~ spl3_3
    | spl3_21
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f201,f127,f205,f80,f133])).

fof(f201,plain,
    ( ! [X0] :
        ( v1_funct_2(k2_funct_1(sK2),sK1,X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_8 ),
    inference(superposition,[],[f66,f170])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f161,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f155,f49])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f155,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl3_13
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f159,plain,
    ( ~ spl3_4
    | ~ spl3_13
    | ~ spl3_5
    | spl3_14
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f152,f116,f85,f157,f88,f154,f85])).

fof(f88,plain,
    ( spl3_5
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f85,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f116,plain,
    ( spl3_7
  <=> sK2 = k7_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f152,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f151,f105])).

fof(f105,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f92,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f92,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f151,plain,
    ( r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),sK0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f63,f119])).

fof(f119,plain,
    ( k2_relat_1(sK2) = k9_relat_1(sK2,sK0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f110,f117])).

fof(f117,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f110,plain,
    ( ! [X5] : k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5)
    | ~ spl3_4 ),
    inference(resolution,[],[f60,f92])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).

fof(f150,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_9 ),
    inference(avatar_split_clause,[],[f149,f133,f88,f85])).

fof(f149,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(resolution,[],[f134,f55])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f134,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f148,plain,
    ( spl3_12
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f144,f85,f146])).

fof(f144,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f46,f143])).

fof(f143,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f58,f49])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f129,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f125,f85,f127])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f46,f124])).

fof(f124,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f118,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f114,f85,f116])).

fof(f114,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK0) ),
    inference(resolution,[],[f68,f106])).

fof(f106,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f70,f48])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f102,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl3_6 ),
    inference(resolution,[],[f95,f59])).

fof(f59,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f95,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl3_6
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f100,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f89,f46])).

fof(f89,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f91,f94,f85])).

fof(f91,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f48])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f90,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | spl3_3 ),
    inference(avatar_split_clause,[],[f83,f80,f88,f85])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(resolution,[],[f56,f81])).

fof(f81,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f80,f77,f74])).

fof(f45,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:22:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (26419)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (26416)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.49  % (26425)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (26418)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.49  % (26414)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.49  % (26416)Refutation not found, incomplete strategy% (26416)------------------------------
% 0.21/0.49  % (26416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (26413)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.49  % (26423)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (26415)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (26433)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (26427)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (26436)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (26417)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (26428)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.50  % (26434)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (26420)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (26432)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (26436)Refutation not found, incomplete strategy% (26436)------------------------------
% 0.21/0.50  % (26436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (26436)Memory used [KB]: 10618
% 0.21/0.50  % (26436)Time elapsed: 0.054 s
% 0.21/0.50  % (26436)------------------------------
% 0.21/0.50  % (26436)------------------------------
% 0.21/0.50  % (26423)Refutation not found, incomplete strategy% (26423)------------------------------
% 0.21/0.50  % (26423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (26425)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (26431)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (26435)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (26424)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (26416)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (26416)Memory used [KB]: 10618
% 0.21/0.51  % (26416)Time elapsed: 0.083 s
% 0.21/0.51  % (26416)------------------------------
% 0.21/0.51  % (26416)------------------------------
% 1.25/0.51  % (26426)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.25/0.51  % (26430)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.25/0.51  % (26423)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.51  
% 1.25/0.51  % (26423)Memory used [KB]: 10618
% 1.25/0.51  % (26423)Time elapsed: 0.103 s
% 1.25/0.51  % (26423)------------------------------
% 1.25/0.51  % (26423)------------------------------
% 1.25/0.51  % (26420)Refutation not found, incomplete strategy% (26420)------------------------------
% 1.25/0.51  % (26420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.51  % (26420)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.51  
% 1.25/0.51  % (26420)Memory used [KB]: 6396
% 1.25/0.51  % (26420)Time elapsed: 0.075 s
% 1.25/0.51  % (26420)------------------------------
% 1.25/0.51  % (26420)------------------------------
% 1.25/0.52  % (26422)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.25/0.52  % (26421)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f512,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(avatar_sat_refutation,[],[f82,f90,f96,f100,f102,f118,f129,f148,f150,f159,f161,f207,f251,f271,f286,f477,f511])).
% 1.25/0.52  fof(f511,plain,(
% 1.25/0.52    spl3_2 | ~spl3_12 | ~spl3_14 | ~spl3_21),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f509])).
% 1.25/0.52  fof(f509,plain,(
% 1.25/0.52    $false | (spl3_2 | ~spl3_12 | ~spl3_14 | ~spl3_21)),
% 1.25/0.52    inference(resolution,[],[f496,f158])).
% 1.25/0.52  fof(f158,plain,(
% 1.25/0.52    r1_tarski(k1_relat_1(sK2),sK0) | ~spl3_14),
% 1.25/0.52    inference(avatar_component_clause,[],[f157])).
% 1.25/0.52  fof(f157,plain,(
% 1.25/0.52    spl3_14 <=> r1_tarski(k1_relat_1(sK2),sK0)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.25/0.52  fof(f496,plain,(
% 1.25/0.52    ~r1_tarski(k1_relat_1(sK2),sK0) | (spl3_2 | ~spl3_12 | ~spl3_21)),
% 1.25/0.52    inference(resolution,[],[f495,f78])).
% 1.25/0.52  fof(f78,plain,(
% 1.25/0.52    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 1.25/0.52    inference(avatar_component_clause,[],[f77])).
% 1.25/0.52  fof(f77,plain,(
% 1.25/0.52    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.25/0.52  fof(f495,plain,(
% 1.25/0.52    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | (~spl3_12 | ~spl3_21)),
% 1.25/0.52    inference(forward_demodulation,[],[f206,f147])).
% 1.25/0.52  fof(f147,plain,(
% 1.25/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_12),
% 1.25/0.52    inference(avatar_component_clause,[],[f146])).
% 1.25/0.52  fof(f146,plain,(
% 1.25/0.52    spl3_12 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.25/0.52  fof(f206,plain,(
% 1.25/0.52    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0)) ) | ~spl3_21),
% 1.25/0.52    inference(avatar_component_clause,[],[f205])).
% 1.25/0.52  fof(f205,plain,(
% 1.25/0.52    spl3_21 <=> ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.25/0.52  fof(f477,plain,(
% 1.25/0.52    ~spl3_27 | ~spl3_31),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f469])).
% 1.25/0.52  fof(f469,plain,(
% 1.25/0.52    $false | (~spl3_27 | ~spl3_31)),
% 1.25/0.52    inference(resolution,[],[f270,f247])).
% 1.25/0.52  fof(f247,plain,(
% 1.25/0.52    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl3_27),
% 1.25/0.52    inference(avatar_component_clause,[],[f246])).
% 1.25/0.52  fof(f246,plain,(
% 1.25/0.52    spl3_27 <=> ! [X0] : ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.25/0.52  fof(f270,plain,(
% 1.25/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_31),
% 1.25/0.52    inference(avatar_component_clause,[],[f269])).
% 1.25/0.52  fof(f269,plain,(
% 1.25/0.52    spl3_31 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.25/0.52  fof(f286,plain,(
% 1.25/0.52    ~spl3_12 | ~spl3_14 | spl3_28),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f285])).
% 1.25/0.52  fof(f285,plain,(
% 1.25/0.52    $false | (~spl3_12 | ~spl3_14 | spl3_28)),
% 1.25/0.52    inference(resolution,[],[f257,f158])).
% 1.25/0.52  fof(f257,plain,(
% 1.25/0.52    ~r1_tarski(k1_relat_1(sK2),sK0) | (~spl3_12 | spl3_28)),
% 1.25/0.52    inference(backward_demodulation,[],[f250,f147])).
% 1.25/0.52  fof(f250,plain,(
% 1.25/0.52    ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | spl3_28),
% 1.25/0.52    inference(avatar_component_clause,[],[f249])).
% 1.25/0.52  fof(f249,plain,(
% 1.25/0.52    spl3_28 <=> r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.25/0.52  fof(f271,plain,(
% 1.25/0.52    ~spl3_9 | ~spl3_3 | spl3_31 | ~spl3_8 | ~spl3_12),
% 1.25/0.52    inference(avatar_split_clause,[],[f267,f146,f127,f269,f80,f133])).
% 1.25/0.52  fof(f133,plain,(
% 1.25/0.52    spl3_9 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.25/0.52  fof(f80,plain,(
% 1.25/0.52    spl3_3 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.25/0.52  fof(f127,plain,(
% 1.25/0.52    spl3_8 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.25/0.52  fof(f267,plain,(
% 1.25/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_8 | ~spl3_12)),
% 1.25/0.52    inference(forward_demodulation,[],[f259,f170])).
% 1.25/0.52  fof(f170,plain,(
% 1.25/0.52    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl3_8),
% 1.25/0.52    inference(backward_demodulation,[],[f128,f169])).
% 1.25/0.52  fof(f169,plain,(
% 1.25/0.52    sK1 = k2_relat_1(sK2)),
% 1.25/0.52    inference(forward_demodulation,[],[f167,f50])).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.25/0.52    inference(flattening,[],[f19])).
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.25/0.52    inference(ennf_transformation,[],[f18])).
% 1.25/0.52  fof(f18,negated_conjecture,(
% 1.25/0.52    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.25/0.52    inference(negated_conjecture,[],[f17])).
% 1.25/0.52  fof(f17,conjecture,(
% 1.25/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.25/0.52  fof(f167,plain,(
% 1.25/0.52    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.25/0.52    inference(resolution,[],[f69,f48])).
% 1.25/0.52  fof(f48,plain,(
% 1.25/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f69,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f41])).
% 1.25/0.52  fof(f41,plain,(
% 1.25/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f13])).
% 1.25/0.52  fof(f13,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.25/0.52  fof(f128,plain,(
% 1.25/0.52    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_8),
% 1.25/0.52    inference(avatar_component_clause,[],[f127])).
% 1.25/0.52  fof(f259,plain,(
% 1.25/0.52    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_12),
% 1.25/0.52    inference(superposition,[],[f54,f147])).
% 1.25/0.52  fof(f54,plain,(
% 1.25/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f24])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f15])).
% 1.25/0.52  fof(f15,axiom,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 1.25/0.52  fof(f251,plain,(
% 1.25/0.52    spl3_27 | ~spl3_28 | spl3_1),
% 1.25/0.52    inference(avatar_split_clause,[],[f240,f74,f249,f246])).
% 1.25/0.52  fof(f74,plain,(
% 1.25/0.52    spl3_1 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.25/0.52  fof(f240,plain,(
% 1.25/0.52    ( ! [X0] : (~r1_tarski(k2_relat_1(k2_funct_1(sK2)),sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | spl3_1),
% 1.25/0.52    inference(resolution,[],[f72,f75])).
% 1.25/0.52  fof(f75,plain,(
% 1.25/0.52    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_1),
% 1.25/0.52    inference(avatar_component_clause,[],[f74])).
% 1.25/0.52  fof(f72,plain,(
% 1.25/0.52    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f44])).
% 1.25/0.52  fof(f44,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.25/0.52    inference(flattening,[],[f43])).
% 1.25/0.52  fof(f43,plain,(
% 1.25/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.25/0.52    inference(ennf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,axiom,(
% 1.25/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).
% 1.25/0.52  fof(f207,plain,(
% 1.25/0.52    ~spl3_9 | ~spl3_3 | spl3_21 | ~spl3_8),
% 1.25/0.52    inference(avatar_split_clause,[],[f201,f127,f205,f80,f133])).
% 1.25/0.52  fof(f201,plain,(
% 1.25/0.52    ( ! [X0] : (v1_funct_2(k2_funct_1(sK2),sK1,X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_8),
% 1.25/0.52    inference(superposition,[],[f66,f170])).
% 1.25/0.52  fof(f66,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f38])).
% 1.25/0.52  fof(f38,plain,(
% 1.25/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f37])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f16])).
% 1.25/0.52  fof(f16,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 1.25/0.52  fof(f161,plain,(
% 1.25/0.52    spl3_13),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f160])).
% 1.25/0.52  fof(f160,plain,(
% 1.25/0.52    $false | spl3_13),
% 1.25/0.52    inference(resolution,[],[f155,f49])).
% 1.25/0.52  fof(f49,plain,(
% 1.25/0.52    v2_funct_1(sK2)),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f155,plain,(
% 1.25/0.52    ~v2_funct_1(sK2) | spl3_13),
% 1.25/0.52    inference(avatar_component_clause,[],[f154])).
% 1.25/0.52  fof(f154,plain,(
% 1.25/0.52    spl3_13 <=> v2_funct_1(sK2)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.25/0.52  fof(f159,plain,(
% 1.25/0.52    ~spl3_4 | ~spl3_13 | ~spl3_5 | spl3_14 | ~spl3_4 | ~spl3_7),
% 1.25/0.52    inference(avatar_split_clause,[],[f152,f116,f85,f157,f88,f154,f85])).
% 1.25/0.52  fof(f88,plain,(
% 1.25/0.52    spl3_5 <=> v1_funct_1(sK2)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.25/0.52  fof(f85,plain,(
% 1.25/0.52    spl3_4 <=> v1_relat_1(sK2)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.25/0.52  fof(f116,plain,(
% 1.25/0.52    spl3_7 <=> sK2 = k7_relat_1(sK2,sK0)),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.25/0.52  fof(f152,plain,(
% 1.25/0.52    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_7)),
% 1.25/0.52    inference(forward_demodulation,[],[f151,f105])).
% 1.25/0.52  fof(f105,plain,(
% 1.25/0.52    k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) | ~spl3_4),
% 1.25/0.52    inference(resolution,[],[f92,f51])).
% 1.25/0.52  fof(f51,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f21])).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f5])).
% 1.25/0.52  fof(f5,axiom,(
% 1.25/0.52    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).
% 1.25/0.52  fof(f92,plain,(
% 1.25/0.52    v1_relat_1(sK2) | ~spl3_4),
% 1.25/0.52    inference(avatar_component_clause,[],[f85])).
% 1.25/0.52  fof(f151,plain,(
% 1.25/0.52    r1_tarski(k10_relat_1(sK2,k2_relat_1(sK2)),sK0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_7)),
% 1.25/0.52    inference(superposition,[],[f63,f119])).
% 1.25/0.52  fof(f119,plain,(
% 1.25/0.52    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) | (~spl3_4 | ~spl3_7)),
% 1.25/0.52    inference(superposition,[],[f110,f117])).
% 1.25/0.52  fof(f117,plain,(
% 1.25/0.52    sK2 = k7_relat_1(sK2,sK0) | ~spl3_7),
% 1.25/0.52    inference(avatar_component_clause,[],[f116])).
% 1.25/0.52  fof(f110,plain,(
% 1.25/0.52    ( ! [X5] : (k2_relat_1(k7_relat_1(sK2,X5)) = k9_relat_1(sK2,X5)) ) | ~spl3_4),
% 1.25/0.52    inference(resolution,[],[f60,f92])).
% 1.25/0.52  fof(f60,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(ennf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 1.25/0.52  fof(f63,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f31])).
% 1.25/0.52  fof(f31,plain,(
% 1.25/0.52    ! [X0,X1] : ((r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f9])).
% 1.25/0.52  fof(f9,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => r1_tarski(k10_relat_1(X1,k9_relat_1(X1,X0)),X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_funct_1)).
% 1.25/0.52  fof(f150,plain,(
% 1.25/0.52    ~spl3_4 | ~spl3_5 | spl3_9),
% 1.25/0.52    inference(avatar_split_clause,[],[f149,f133,f88,f85])).
% 1.25/0.52  fof(f149,plain,(
% 1.25/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_9),
% 1.25/0.52    inference(resolution,[],[f134,f55])).
% 1.25/0.52  fof(f55,plain,(
% 1.25/0.52    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f26])).
% 1.25/0.52  fof(f26,plain,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f25])).
% 1.25/0.52  fof(f25,plain,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f7])).
% 1.25/0.52  fof(f7,axiom,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.25/0.52  fof(f134,plain,(
% 1.25/0.52    ~v1_relat_1(k2_funct_1(sK2)) | spl3_9),
% 1.25/0.52    inference(avatar_component_clause,[],[f133])).
% 1.25/0.52  fof(f148,plain,(
% 1.25/0.52    spl3_12 | ~spl3_4),
% 1.25/0.52    inference(avatar_split_clause,[],[f144,f85,f146])).
% 1.25/0.52  fof(f144,plain,(
% 1.25/0.52    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    inference(global_subsumption,[],[f46,f143])).
% 1.25/0.52  fof(f143,plain,(
% 1.25/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    inference(resolution,[],[f58,f49])).
% 1.25/0.52  fof(f58,plain,(
% 1.25/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f28])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f11])).
% 1.25/0.52  fof(f11,axiom,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.25/0.52  fof(f46,plain,(
% 1.25/0.52    v1_funct_1(sK2)),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  fof(f129,plain,(
% 1.25/0.52    spl3_8 | ~spl3_4),
% 1.25/0.52    inference(avatar_split_clause,[],[f125,f85,f127])).
% 1.25/0.52  fof(f125,plain,(
% 1.25/0.52    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    inference(global_subsumption,[],[f46,f124])).
% 1.25/0.52  fof(f124,plain,(
% 1.25/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.25/0.52    inference(resolution,[],[f57,f49])).
% 1.25/0.52  fof(f57,plain,(
% 1.25/0.52    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f28])).
% 1.25/0.52  fof(f118,plain,(
% 1.25/0.52    spl3_7 | ~spl3_4),
% 1.25/0.52    inference(avatar_split_clause,[],[f114,f85,f116])).
% 1.25/0.52  fof(f114,plain,(
% 1.25/0.52    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK0)),
% 1.25/0.52    inference(resolution,[],[f68,f106])).
% 1.25/0.52  fof(f106,plain,(
% 1.25/0.52    v4_relat_1(sK2,sK0)),
% 1.25/0.52    inference(resolution,[],[f70,f48])).
% 1.25/0.52  fof(f70,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f42])).
% 1.25/0.52  fof(f42,plain,(
% 1.25/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.52    inference(ennf_transformation,[],[f12])).
% 1.25/0.52  fof(f12,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.25/0.52  fof(f68,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f40])).
% 1.25/0.52  fof(f40,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.52    inference(flattening,[],[f39])).
% 1.25/0.52  fof(f39,plain,(
% 1.25/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.25/0.52  fof(f102,plain,(
% 1.25/0.52    spl3_6),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f101])).
% 1.25/0.52  fof(f101,plain,(
% 1.25/0.52    $false | spl3_6),
% 1.25/0.52    inference(resolution,[],[f95,f59])).
% 1.25/0.52  fof(f59,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f3])).
% 1.25/0.52  fof(f3,axiom,(
% 1.25/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.25/0.52  fof(f95,plain,(
% 1.25/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_6),
% 1.25/0.52    inference(avatar_component_clause,[],[f94])).
% 1.25/0.52  fof(f94,plain,(
% 1.25/0.52    spl3_6 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.25/0.52  fof(f100,plain,(
% 1.25/0.52    spl3_5),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f99])).
% 1.25/0.52  fof(f99,plain,(
% 1.25/0.52    $false | spl3_5),
% 1.25/0.52    inference(resolution,[],[f89,f46])).
% 1.25/0.52  fof(f89,plain,(
% 1.25/0.52    ~v1_funct_1(sK2) | spl3_5),
% 1.25/0.52    inference(avatar_component_clause,[],[f88])).
% 1.25/0.52  fof(f96,plain,(
% 1.25/0.52    spl3_4 | ~spl3_6),
% 1.25/0.52    inference(avatar_split_clause,[],[f91,f94,f85])).
% 1.25/0.52  fof(f91,plain,(
% 1.25/0.52    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.25/0.52    inference(resolution,[],[f52,f48])).
% 1.25/0.52  fof(f52,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f22])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.25/0.52  fof(f90,plain,(
% 1.25/0.52    ~spl3_4 | ~spl3_5 | spl3_3),
% 1.25/0.52    inference(avatar_split_clause,[],[f83,f80,f88,f85])).
% 1.25/0.52  fof(f83,plain,(
% 1.25/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_3),
% 1.25/0.52    inference(resolution,[],[f56,f81])).
% 1.25/0.52  fof(f81,plain,(
% 1.25/0.52    ~v1_funct_1(k2_funct_1(sK2)) | spl3_3),
% 1.25/0.52    inference(avatar_component_clause,[],[f80])).
% 1.25/0.52  fof(f56,plain,(
% 1.25/0.52    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f26])).
% 1.25/0.52  fof(f82,plain,(
% 1.25/0.52    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.25/0.52    inference(avatar_split_clause,[],[f45,f80,f77,f74])).
% 1.25/0.52  fof(f45,plain,(
% 1.25/0.52    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.25/0.52    inference(cnf_transformation,[],[f20])).
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (26425)------------------------------
% 1.25/0.52  % (26425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (26425)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (26425)Memory used [KB]: 10874
% 1.25/0.52  % (26425)Time elapsed: 0.102 s
% 1.25/0.52  % (26425)------------------------------
% 1.25/0.52  % (26425)------------------------------
% 1.25/0.53  % (26409)Success in time 0.17 s
%------------------------------------------------------------------------------
