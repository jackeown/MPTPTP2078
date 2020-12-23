%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 215 expanded)
%              Number of leaves         :   14 (  59 expanded)
%              Depth                    :   17
%              Number of atoms          :  293 ( 712 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f154,f291,f341,f385])).

fof(f385,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f384])).

fof(f384,plain,
    ( $false
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f381,f31])).

fof(f31,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
    & r1_tarski(sK0,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
        & r1_tarski(X0,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)
      & r1_tarski(sK0,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)
      & r1_tarski(X0,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X0,X2)
         => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X0,X2)
       => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

fof(f381,plain,
    ( ~ r1_tarski(sK0,sK2)
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f370,f30])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f370,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ r1_tarski(X3,sK2) )
    | ~ spl5_1
    | spl5_3 ),
    inference(resolution,[],[f364,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f364,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ r1_tarski(X0,sK2) )
    | ~ spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f361,f145])).

fof(f145,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl5_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl5_3 ),
    inference(resolution,[],[f296,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f296,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_relat_1(sK3),X2)
        | ~ r1_tarski(X2,sK2) )
    | spl5_3 ),
    inference(resolution,[],[f286,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f286,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl5_3
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f341,plain,
    ( ~ spl5_1
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f337])).

fof(f337,plain,
    ( $false
    | ~ spl5_1
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f30,f332,f37])).

fof(f332,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f329,f145])).

fof(f329,plain,
    ( ~ v4_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_1
    | spl5_4 ),
    inference(resolution,[],[f322,f34])).

fof(f322,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl5_1
    | spl5_4 ),
    inference(subsumption_resolution,[],[f318,f145])).

fof(f318,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl5_4 ),
    inference(resolution,[],[f311,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(k7_relat_1(X1,X0),X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f33,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f311,plain,
    ( ~ sQ4_eqProxy(k7_relat_1(sK3,sK0),sK3)
    | spl5_4 ),
    inference(resolution,[],[f290,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( sQ4_eqProxy(X1,X0)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f43])).

fof(f290,plain,
    ( ~ sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl5_4
  <=> sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f291,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f280,f148,f144,f288,f284])).

fof(f148,plain,
    ( spl5_2
  <=> ! [X6] :
        ( ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X6))
        | ~ r1_tarski(k1_relat_1(sK3),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f280,plain,
    ( ~ sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0))
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f274,f145])).

fof(f274,plain,
    ( ~ sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0))
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f195,f44])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k7_relat_1(sK3,sK2),X0)
        | ~ sQ4_eqProxy(X0,k7_relat_1(sK3,sK0)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f191,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(X0,X2)
      | ~ sQ4_eqProxy(X1,X2)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f43])).

fof(f191,plain,
    ( ~ sQ4_eqProxy(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f190,plain,
    ( ~ sQ4_eqProxy(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK0))
    | ~ v1_funct_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f184,f30])).

fof(f184,plain,
    ( ~ sQ4_eqProxy(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f175,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( sQ4_eqProxy(k2_partfun1(X0,X1,X2,X3),k7_relat_1(X2,X3))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_proxy_replacement,[],[f39,f43])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f175,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),X0)
        | ~ sQ4_eqProxy(X0,k7_relat_1(sK3,sK0)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f172,f62])).

fof(f172,plain,
    ( ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,sK0))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f164,f30])).

fof(f164,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X3)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f160,f37])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK3,X0)
        | ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X0)) )
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f157,f145])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X0))
        | ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | ~ spl5_2 ),
    inference(resolution,[],[f149,f34])).

fof(f149,plain,
    ( ! [X6] :
        ( ~ r1_tarski(k1_relat_1(sK3),X6)
        | ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X6)) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f148])).

fof(f154,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f30,f146,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f146,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f144])).

fof(f150,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f88,f148,f144])).

fof(f88,plain,(
    ! [X6] :
      ( ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X6))
      | ~ r1_tarski(k1_relat_1(sK3),X6)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f75,f44])).

fof(f75,plain,(
    ! [X0] :
      ( ~ sQ4_eqProxy(X0,sK3)
      | ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),X0) ) ),
    inference(resolution,[],[f74,f62])).

fof(f74,plain,(
    ~ sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ~ sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f70,f60])).

fof(f60,plain,(
    ! [X0] : sQ4_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f43])).

fof(f70,plain,
    ( ~ sQ4_eqProxy(sK0,sK0)
    | ~ sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f69,f60])).

fof(f69,plain,
    ( ~ sQ4_eqProxy(sK1,sK1)
    | ~ sQ4_eqProxy(sK0,sK0)
    | ~ sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f67,f60])).

fof(f67,plain,
    ( ~ sQ4_eqProxy(sK3,sK3)
    | ~ sQ4_eqProxy(sK1,sK1)
    | ~ sQ4_eqProxy(sK0,sK0)
    | ~ sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2)) ),
    inference(resolution,[],[f65,f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sQ4_eqProxy(X0,sK3)
      | ~ sQ4_eqProxy(X1,sK1)
      | ~ sQ4_eqProxy(X2,sK0)
      | ~ sQ4_eqProxy(X0,k2_partfun1(sK0,sK1,sK3,sK2)) ) ),
    inference(resolution,[],[f64,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f41])).

% (30241)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X3,X0,X1,X2)
      | ~ sQ4_eqProxy(X1,k2_partfun1(sK0,sK1,sK3,sK2))
      | ~ sQ4_eqProxy(X2,sK3)
      | ~ sQ4_eqProxy(X0,sK1)
      | ~ sQ4_eqProxy(X3,sK0) ) ),
    inference(resolution,[],[f57,f32])).

fof(f32,plain,(
    ~ r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_relset_1(X1,X3,X5,X7)
      | ~ sQ4_eqProxy(X2,X3)
      | ~ sQ4_eqProxy(X4,X5)
      | ~ sQ4_eqProxy(X6,X7)
      | ~ r2_relset_1(X0,X2,X4,X6)
      | ~ sQ4_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:12:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (30231)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (30223)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (30223)Refutation not found, incomplete strategy% (30223)------------------------------
% 0.21/0.48  % (30223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (30223)Memory used [KB]: 10618
% 0.21/0.48  % (30223)Time elapsed: 0.061 s
% 0.21/0.48  % (30223)------------------------------
% 0.21/0.48  % (30223)------------------------------
% 0.21/0.50  % (30232)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (30231)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f150,f154,f291,f341,f385])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    ~spl5_1 | spl5_3),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f384])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    $false | (~spl5_1 | spl5_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f381,f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    r1_tarski(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3) & r1_tarski(sK0,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3) & r1_tarski(X0,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X0,X2) => r2_relset_1(X0,X1,k2_partfun1(X0,X1,X3,X2),X3)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK2) | (~spl5_1 | spl5_3)),
% 0.21/0.50    inference(resolution,[],[f370,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~r1_tarski(X3,sK2)) ) | (~spl5_1 | spl5_3)),
% 0.21/0.50    inference(resolution,[],[f364,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f364,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~r1_tarski(X0,sK2)) ) | (~spl5_1 | spl5_3)),
% 0.21/0.50    inference(subsumption_resolution,[],[f361,f145])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f144])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    spl5_1 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_tarski(X0,sK2) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl5_3),
% 0.21/0.50    inference(resolution,[],[f296,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    ( ! [X2] : (~r1_tarski(k1_relat_1(sK3),X2) | ~r1_tarski(X2,sK2)) ) | spl5_3),
% 0.21/0.50    inference(resolution,[],[f286,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK3),sK2) | spl5_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f284])).
% 0.21/0.50  fof(f284,plain,(
% 0.21/0.50    spl5_3 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    ~spl5_1 | spl5_4),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f337])).
% 0.21/0.50  fof(f337,plain,(
% 0.21/0.50    $false | (~spl5_1 | spl5_4)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f30,f332,f37])).
% 0.21/0.50  fof(f332,plain,(
% 0.21/0.50    ~v4_relat_1(sK3,sK0) | (~spl5_1 | spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f329,f145])).
% 0.21/0.50  fof(f329,plain,(
% 0.21/0.50    ~v4_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | (~spl5_1 | spl5_4)),
% 0.21/0.50    inference(resolution,[],[f322,f34])).
% 0.21/0.50  fof(f322,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK3),sK0) | (~spl5_1 | spl5_4)),
% 0.21/0.50    inference(subsumption_resolution,[],[f318,f145])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ~r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl5_4),
% 0.21/0.50    inference(resolution,[],[f311,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sQ4_eqProxy(k7_relat_1(X1,X0),X1) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f33,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ~sQ4_eqProxy(k7_relat_1(sK3,sK0),sK3) | spl5_4),
% 0.21/0.50    inference(resolution,[],[f290,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sQ4_eqProxy(X1,X0) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f43])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0)) | spl5_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f288])).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    spl5_4 <=> sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    ~spl5_3 | ~spl5_4 | ~spl5_1 | ~spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f280,f148,f144,f288,f284])).
% 0.21/0.50  fof(f148,plain,(
% 0.21/0.50    spl5_2 <=> ! [X6] : (~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X6)) | ~r1_tarski(k1_relat_1(sK3),X6))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0)) | ~r1_tarski(k1_relat_1(sK3),sK2) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f274,f145])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK3,k7_relat_1(sK3,sK0)) | ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(resolution,[],[f195,f44])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ( ! [X0] : (~sQ4_eqProxy(k7_relat_1(sK3,sK2),X0) | ~sQ4_eqProxy(X0,k7_relat_1(sK3,sK0))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(resolution,[],[f191,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ4_eqProxy(X0,X2) | ~sQ4_eqProxy(X1,X2) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f43])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~sQ4_eqProxy(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK0)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ~sQ4_eqProxy(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK0)) | ~v1_funct_1(sK3) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f184,f30])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~sQ4_eqProxy(k7_relat_1(sK3,sK2),k7_relat_1(sK3,sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(resolution,[],[f175,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (sQ4_eqProxy(k2_partfun1(X0,X1,X2,X3),k7_relat_1(X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f39,f43])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X0] : (~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),X0) | ~sQ4_eqProxy(X0,k7_relat_1(sK3,sK0))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(resolution,[],[f172,f62])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,sK0)) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(resolution,[],[f164,f30])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X3))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(resolution,[],[f160,f37])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X0] : (~v4_relat_1(sK3,X0) | ~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X0))) ) | (~spl5_1 | ~spl5_2)),
% 0.21/0.50    inference(subsumption_resolution,[],[f157,f145])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X0] : (~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X0)) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | ~spl5_2),
% 0.21/0.50    inference(resolution,[],[f149,f34])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X6] : (~r1_tarski(k1_relat_1(sK3),X6) | ~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X6))) ) | ~spl5_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f148])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl5_1),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f151])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    $false | spl5_1),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f30,f146,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ~v1_relat_1(sK3) | spl5_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f144])).
% 0.21/0.50  fof(f150,plain,(
% 0.21/0.50    ~spl5_1 | spl5_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f88,f148,f144])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X6] : (~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),k7_relat_1(sK3,X6)) | ~r1_tarski(k1_relat_1(sK3),X6) | ~v1_relat_1(sK3)) )),
% 0.21/0.50    inference(resolution,[],[f75,f44])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (~sQ4_eqProxy(X0,sK3) | ~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),X0)) )),
% 0.21/0.50    inference(resolution,[],[f74,f62])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~sQ4_eqProxy(k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.21/0.50    inference(resolution,[],[f71,f61])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f70,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (sQ4_eqProxy(X0,X0)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f43])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK0,sK0) | ~sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f69,f60])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK1,sK1) | ~sQ4_eqProxy(sK0,sK0) | ~sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f67,f60])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~sQ4_eqProxy(sK3,sK3) | ~sQ4_eqProxy(sK1,sK1) | ~sQ4_eqProxy(sK0,sK0) | ~sQ4_eqProxy(sK3,k2_partfun1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(resolution,[],[f65,f30])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sQ4_eqProxy(X0,sK3) | ~sQ4_eqProxy(X1,sK1) | ~sQ4_eqProxy(X2,sK0) | ~sQ4_eqProxy(X0,k2_partfun1(sK0,sK1,sK3,sK2))) )),
% 0.21/0.50    inference(resolution,[],[f64,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(equality_resolution,[],[f41])).
% 0.21/0.50  % (30241)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(nnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X3,X0,X1,X2) | ~sQ4_eqProxy(X1,k2_partfun1(sK0,sK1,sK3,sK2)) | ~sQ4_eqProxy(X2,sK3) | ~sQ4_eqProxy(X0,sK1) | ~sQ4_eqProxy(X3,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f57,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ~r2_relset_1(sK0,sK1,k2_partfun1(sK0,sK1,sK3,sK2),sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_relset_1(X1,X3,X5,X7) | ~sQ4_eqProxy(X2,X3) | ~sQ4_eqProxy(X4,X5) | ~sQ4_eqProxy(X6,X7) | ~r2_relset_1(X0,X2,X4,X6) | ~sQ4_eqProxy(X0,X1)) )),
% 0.21/0.50    inference(equality_proxy_axiom,[],[f43])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (30231)------------------------------
% 0.21/0.50  % (30231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (30231)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (30231)Memory used [KB]: 6780
% 0.21/0.50  % (30231)Time elapsed: 0.083 s
% 0.21/0.50  % (30231)------------------------------
% 0.21/0.50  % (30231)------------------------------
% 0.21/0.50  % (30216)Success in time 0.145 s
%------------------------------------------------------------------------------
