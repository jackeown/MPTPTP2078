%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:44 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 297 expanded)
%              Number of leaves         :   18 (  87 expanded)
%              Depth                    :   10
%              Number of atoms          :  286 (1116 expanded)
%              Number of equality atoms :   47 ( 268 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (26865)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
fof(f857,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f103,f105,f565,f635,f685,f687,f744,f856])).

fof(f856,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_24 ),
    inference(avatar_contradiction_clause,[],[f855])).

fof(f855,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_4
    | ~ spl4_24 ),
    inference(unit_resulting_resolution,[],[f751,f68,f848,f476,f851,f381])).

fof(f381,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(o_0_0_xboole_0,X1,X3),X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,o_0_0_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_funct_2(X3,o_0_0_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f81,f79])).

fof(f79,plain,(
    ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != X0
      | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f36,f36])).

fof(f36,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,o_0_0_xboole_0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1)))
      | ~ r1_tarski(k2_relset_1(o_0_0_xboole_0,X1,X3),X2)
      | v1_funct_2(X3,o_0_0_xboole_0,X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | o_0_0_xboole_0 != X0
      | v1_funct_2(X3,X0,X2) ) ),
    inference(definition_unfolding,[],[f59,f36])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 != X0
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f851,plain,
    ( ~ v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,sK2)
    | ~ spl4_1
    | spl4_4
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f690,f640])).

fof(f640,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl4_24
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f690,plain,
    ( ~ v1_funct_2(sK3,o_0_0_xboole_0,sK2)
    | ~ spl4_1
    | spl4_4 ),
    inference(superposition,[],[f98,f85])).

fof(f85,plain,
    ( o_0_0_xboole_0 = sK0
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f98,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_4
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f476,plain,(
    ! [X6,X7] : r1_tarski(k2_relset_1(X6,o_0_0_xboole_0,o_0_0_xboole_0),X7) ),
    inference(resolution,[],[f456,f219])).

fof(f219,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,o_0_0_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f58,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f456,plain,(
    ! [X6,X5] : r1_tarski(k2_relset_1(X5,X6,o_0_0_xboole_0),X6) ),
    inference(resolution,[],[f338,f68])).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relset_1(X1,X2,X0),X2) ) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f848,plain,
    ( v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f847,f640])).

fof(f847,plain,
    ( v1_funct_2(sK3,o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f688,f88])).

fof(f88,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_2
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f688,plain,
    ( v1_funct_2(sK3,o_0_0_xboole_0,sK1)
    | ~ spl4_1 ),
    inference(superposition,[],[f33,f85])).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f41,f63])).

fof(f63,plain,(
    ! [X0] : o_0_0_xboole_0 = k1_subset_1(X0) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f751,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl4_24 ),
    inference(superposition,[],[f32,f640])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f744,plain,
    ( spl4_24
    | ~ spl4_25
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f743,f83,f642,f638])).

fof(f642,plain,
    ( spl4_25
  <=> r1_tarski(o_0_0_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f743,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK3)
    | o_0_0_xboole_0 = sK3
    | ~ spl4_1 ),
    inference(resolution,[],[f702,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f702,plain,
    ( r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f691,f79])).

fof(f691,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl4_1 ),
    inference(superposition,[],[f108,f85])).

fof(f108,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f50,f34])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f687,plain,
    ( spl4_2
    | spl4_4 ),
    inference(avatar_contradiction_clause,[],[f686])).

fof(f686,plain,
    ( $false
    | spl4_2
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f32,f89,f33,f34,f461,f98,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | o_0_0_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(definition_unfolding,[],[f61,f36])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | v1_funct_2(X3,X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f461,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(resolution,[],[f458,f221])).

fof(f221,plain,(
    ! [X7] :
      ( ~ r1_tarski(X7,sK1)
      | r1_tarski(X7,sK2) ) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f458,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) ),
    inference(resolution,[],[f338,f34])).

fof(f89,plain,
    ( o_0_0_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f685,plain,(
    spl4_25 ),
    inference(avatar_contradiction_clause,[],[f675])).

fof(f675,plain,
    ( $false
    | spl4_25 ),
    inference(unit_resulting_resolution,[],[f68,f644,f50])).

fof(f644,plain,
    ( ~ r1_tarski(o_0_0_xboole_0,sK3)
    | spl4_25 ),
    inference(avatar_component_clause,[],[f642])).

fof(f635,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f622])).

fof(f622,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f587,f588])).

fof(f588,plain,
    ( r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f575,f79])).

fof(f575,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(o_0_0_xboole_0,sK1))
    | ~ spl4_1 ),
    inference(superposition,[],[f108,f85])).

fof(f587,plain,
    ( ~ r1_tarski(sK3,o_0_0_xboole_0)
    | ~ spl4_1
    | spl4_3 ),
    inference(forward_demodulation,[],[f574,f79])).

fof(f574,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(o_0_0_xboole_0,sK2))
    | ~ spl4_1
    | spl4_3 ),
    inference(superposition,[],[f106,f85])).

fof(f106,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | spl4_3 ),
    inference(resolution,[],[f49,f94])).

fof(f94,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f565,plain,
    ( spl4_2
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f556])).

fof(f556,plain,
    ( $false
    | spl4_2
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f32,f89,f33,f94,f461,f34,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | o_0_0_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(definition_unfolding,[],[f62,f36])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relset_1(X0,X1,X3),X2)
      | k1_xboole_0 = X1
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f32,f102])).

fof(f102,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_5
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f103,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f30,f100,f96,f92])).

fof(f30,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f19])).

fof(f90,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f64,f87,f83])).

fof(f64,plain,
    ( o_0_0_xboole_0 != sK1
    | o_0_0_xboole_0 = sK0 ),
    inference(definition_unfolding,[],[f31,f36,f36])).

fof(f31,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:20:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (26857)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (26864)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (26878)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (26872)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (26870)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (26851)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (26854)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (26852)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (26852)Refutation not found, incomplete strategy% (26852)------------------------------
% 0.21/0.54  % (26852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26852)Memory used [KB]: 1663
% 0.21/0.54  % (26852)Time elapsed: 0.127 s
% 0.21/0.54  % (26852)------------------------------
% 0.21/0.54  % (26852)------------------------------
% 0.21/0.54  % (26874)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.54  % (26866)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.54  % (26864)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  % (26865)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.40/0.54  fof(f857,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f90,f103,f105,f565,f635,f685,f687,f744,f856])).
% 1.40/0.54  fof(f856,plain,(
% 1.40/0.54    ~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_24),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f855])).
% 1.40/0.54  fof(f855,plain,(
% 1.40/0.54    $false | (~spl4_1 | ~spl4_2 | spl4_4 | ~spl4_24)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f751,f68,f848,f476,f851,f381])).
% 1.40/0.54  fof(f381,plain,(
% 1.40/0.54    ( ! [X2,X3,X1] : (~r1_tarski(k2_relset_1(o_0_0_xboole_0,X1,X3),X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,o_0_0_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(o_0_0_xboole_0)) | v1_funct_2(X3,o_0_0_xboole_0,X2)) )),
% 1.40/0.54    inference(forward_demodulation,[],[f81,f79])).
% 1.40/0.54  fof(f79,plain,(
% 1.40/0.54    ( ! [X1] : (o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)) )),
% 1.40/0.54    inference(equality_resolution,[],[f70])).
% 1.40/0.54  fof(f70,plain,(
% 1.40/0.54    ( ! [X0,X1] : (o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f52,f36,f36])).
% 1.40/0.54  fof(f36,plain,(
% 1.40/0.54    k1_xboole_0 = o_0_0_xboole_0),
% 1.40/0.54    inference(cnf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    k1_xboole_0 = o_0_0_xboole_0),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).
% 1.40/0.54  fof(f52,plain,(
% 1.40/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.40/0.54  fof(f81,plain,(
% 1.40/0.54    ( ! [X2,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,o_0_0_xboole_0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(o_0_0_xboole_0,X1))) | ~r1_tarski(k2_relset_1(o_0_0_xboole_0,X1,X3),X2) | v1_funct_2(X3,o_0_0_xboole_0,X2)) )),
% 1.40/0.54    inference(equality_resolution,[],[f75])).
% 1.40/0.54  fof(f75,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | o_0_0_xboole_0 != X0 | v1_funct_2(X3,X0,X2)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f59,f36])).
% 1.40/0.54  fof(f59,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 != X0 | v1_funct_2(X3,X0,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f29,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.40/0.54    inference(flattening,[],[f28])).
% 1.40/0.54  fof(f28,plain,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.40/0.54    inference(ennf_transformation,[],[f15])).
% 1.40/0.54  fof(f15,axiom,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 1.40/0.54  fof(f851,plain,(
% 1.40/0.54    ~v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,sK2) | (~spl4_1 | spl4_4 | ~spl4_24)),
% 1.40/0.54    inference(forward_demodulation,[],[f690,f640])).
% 1.40/0.54  fof(f640,plain,(
% 1.40/0.54    o_0_0_xboole_0 = sK3 | ~spl4_24),
% 1.40/0.54    inference(avatar_component_clause,[],[f638])).
% 1.40/0.54  fof(f638,plain,(
% 1.40/0.54    spl4_24 <=> o_0_0_xboole_0 = sK3),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.40/0.54  fof(f690,plain,(
% 1.40/0.54    ~v1_funct_2(sK3,o_0_0_xboole_0,sK2) | (~spl4_1 | spl4_4)),
% 1.40/0.54    inference(superposition,[],[f98,f85])).
% 1.40/0.54  fof(f85,plain,(
% 1.40/0.54    o_0_0_xboole_0 = sK0 | ~spl4_1),
% 1.40/0.54    inference(avatar_component_clause,[],[f83])).
% 1.40/0.54  fof(f83,plain,(
% 1.40/0.54    spl4_1 <=> o_0_0_xboole_0 = sK0),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.40/0.54  fof(f98,plain,(
% 1.40/0.54    ~v1_funct_2(sK3,sK0,sK2) | spl4_4),
% 1.40/0.54    inference(avatar_component_clause,[],[f96])).
% 1.40/0.54  fof(f96,plain,(
% 1.40/0.54    spl4_4 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.40/0.54  fof(f476,plain,(
% 1.40/0.54    ( ! [X6,X7] : (r1_tarski(k2_relset_1(X6,o_0_0_xboole_0,o_0_0_xboole_0),X7)) )),
% 1.40/0.54    inference(resolution,[],[f456,f219])).
% 1.40/0.54  fof(f219,plain,(
% 1.40/0.54    ( ! [X2,X3] : (~r1_tarski(X2,o_0_0_xboole_0) | r1_tarski(X2,X3)) )),
% 1.40/0.54    inference(resolution,[],[f58,f67])).
% 1.40/0.54  fof(f67,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f39,f36])).
% 1.40/0.54  fof(f39,plain,(
% 1.40/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.40/0.54  fof(f58,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f27])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.40/0.54    inference(flattening,[],[f26])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.40/0.54    inference(ennf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.40/0.54  fof(f456,plain,(
% 1.40/0.54    ( ! [X6,X5] : (r1_tarski(k2_relset_1(X5,X6,o_0_0_xboole_0),X6)) )),
% 1.40/0.54    inference(resolution,[],[f338,f68])).
% 1.40/0.54  fof(f338,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relset_1(X1,X2,X0),X2)) )),
% 1.40/0.54    inference(resolution,[],[f55,f50])).
% 1.40/0.54  fof(f50,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f8])).
% 1.40/0.54  fof(f8,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.40/0.54  fof(f55,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f24])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(ennf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 1.40/0.54  fof(f848,plain,(
% 1.40/0.54    v1_funct_2(o_0_0_xboole_0,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_24)),
% 1.40/0.54    inference(forward_demodulation,[],[f847,f640])).
% 1.40/0.54  fof(f847,plain,(
% 1.40/0.54    v1_funct_2(sK3,o_0_0_xboole_0,o_0_0_xboole_0) | (~spl4_1 | ~spl4_2)),
% 1.40/0.54    inference(forward_demodulation,[],[f688,f88])).
% 1.40/0.54  fof(f88,plain,(
% 1.40/0.54    o_0_0_xboole_0 = sK1 | ~spl4_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f87])).
% 1.40/0.54  fof(f87,plain,(
% 1.40/0.54    spl4_2 <=> o_0_0_xboole_0 = sK1),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.40/0.54  fof(f688,plain,(
% 1.40/0.54    v1_funct_2(sK3,o_0_0_xboole_0,sK1) | ~spl4_1),
% 1.40/0.54    inference(superposition,[],[f33,f85])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    v1_funct_2(sK3,sK0,sK1)),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.40/0.54    inference(flattening,[],[f18])).
% 1.40/0.54  fof(f18,plain,(
% 1.40/0.54    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.40/0.54    inference(ennf_transformation,[],[f17])).
% 1.40/0.54  fof(f17,negated_conjecture,(
% 1.40/0.54    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.40/0.54    inference(negated_conjecture,[],[f16])).
% 1.40/0.54  fof(f16,conjecture,(
% 1.40/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    ( ! [X0] : (m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f41,f63])).
% 1.40/0.54  fof(f63,plain,(
% 1.40/0.54    ( ! [X0] : (o_0_0_xboole_0 = k1_subset_1(X0)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f40,f36])).
% 1.40/0.54  fof(f40,plain,(
% 1.40/0.54    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f6])).
% 1.40/0.54  fof(f6,axiom,(
% 1.40/0.54    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f7])).
% 1.40/0.54  fof(f7,axiom,(
% 1.40/0.54    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 1.40/0.54  fof(f751,plain,(
% 1.40/0.54    v1_funct_1(o_0_0_xboole_0) | ~spl4_24),
% 1.40/0.54    inference(superposition,[],[f32,f640])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    v1_funct_1(sK3)),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f744,plain,(
% 1.40/0.54    spl4_24 | ~spl4_25 | ~spl4_1),
% 1.40/0.54    inference(avatar_split_clause,[],[f743,f83,f642,f638])).
% 1.40/0.54  fof(f642,plain,(
% 1.40/0.54    spl4_25 <=> r1_tarski(o_0_0_xboole_0,sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.40/0.54  fof(f743,plain,(
% 1.40/0.54    ~r1_tarski(o_0_0_xboole_0,sK3) | o_0_0_xboole_0 = sK3 | ~spl4_1),
% 1.40/0.54    inference(resolution,[],[f702,f48])).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.40/0.54    inference(cnf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.54  fof(f702,plain,(
% 1.40/0.54    r1_tarski(sK3,o_0_0_xboole_0) | ~spl4_1),
% 1.40/0.54    inference(forward_demodulation,[],[f691,f79])).
% 1.40/0.54  fof(f691,plain,(
% 1.40/0.54    r1_tarski(sK3,k2_zfmisc_1(o_0_0_xboole_0,sK1)) | ~spl4_1),
% 1.40/0.54    inference(superposition,[],[f108,f85])).
% 1.40/0.54  fof(f108,plain,(
% 1.40/0.54    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.40/0.54    inference(resolution,[],[f50,f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f687,plain,(
% 1.40/0.54    spl4_2 | spl4_4),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f686])).
% 1.40/0.54  fof(f686,plain,(
% 1.40/0.54    $false | (spl4_2 | spl4_4)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f32,f89,f33,f34,f461,f98,f73])).
% 1.40/0.54  fof(f73,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | o_0_0_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 1.40/0.54    inference(definition_unfolding,[],[f61,f36])).
% 1.40/0.54  fof(f61,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | v1_funct_2(X3,X0,X2)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f461,plain,(
% 1.40/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.40/0.54    inference(resolution,[],[f458,f221])).
% 1.40/0.54  fof(f221,plain,(
% 1.40/0.54    ( ! [X7] : (~r1_tarski(X7,sK1) | r1_tarski(X7,sK2)) )),
% 1.40/0.54    inference(resolution,[],[f58,f35])).
% 1.40/0.54  fof(f35,plain,(
% 1.40/0.54    r1_tarski(sK1,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f458,plain,(
% 1.40/0.54    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1)),
% 1.40/0.54    inference(resolution,[],[f338,f34])).
% 1.40/0.54  fof(f89,plain,(
% 1.40/0.54    o_0_0_xboole_0 != sK1 | spl4_2),
% 1.40/0.54    inference(avatar_component_clause,[],[f87])).
% 1.40/0.54  fof(f685,plain,(
% 1.40/0.54    spl4_25),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f675])).
% 1.40/0.54  fof(f675,plain,(
% 1.40/0.54    $false | spl4_25),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f68,f644,f50])).
% 1.40/0.54  fof(f644,plain,(
% 1.40/0.54    ~r1_tarski(o_0_0_xboole_0,sK3) | spl4_25),
% 1.40/0.54    inference(avatar_component_clause,[],[f642])).
% 1.40/0.54  fof(f635,plain,(
% 1.40/0.54    ~spl4_1 | spl4_3),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f622])).
% 1.40/0.54  fof(f622,plain,(
% 1.40/0.54    $false | (~spl4_1 | spl4_3)),
% 1.40/0.54    inference(subsumption_resolution,[],[f587,f588])).
% 1.40/0.54  fof(f588,plain,(
% 1.40/0.54    r1_tarski(sK3,o_0_0_xboole_0) | ~spl4_1),
% 1.40/0.54    inference(forward_demodulation,[],[f575,f79])).
% 1.40/0.54  fof(f575,plain,(
% 1.40/0.54    r1_tarski(sK3,k2_zfmisc_1(o_0_0_xboole_0,sK1)) | ~spl4_1),
% 1.40/0.54    inference(superposition,[],[f108,f85])).
% 1.40/0.54  fof(f587,plain,(
% 1.40/0.54    ~r1_tarski(sK3,o_0_0_xboole_0) | (~spl4_1 | spl4_3)),
% 1.40/0.54    inference(forward_demodulation,[],[f574,f79])).
% 1.40/0.54  fof(f574,plain,(
% 1.40/0.54    ~r1_tarski(sK3,k2_zfmisc_1(o_0_0_xboole_0,sK2)) | (~spl4_1 | spl4_3)),
% 1.40/0.54    inference(superposition,[],[f106,f85])).
% 1.40/0.54  fof(f106,plain,(
% 1.40/0.54    ~r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | spl4_3),
% 1.40/0.54    inference(resolution,[],[f49,f94])).
% 1.40/0.54  fof(f94,plain,(
% 1.40/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_3),
% 1.40/0.54    inference(avatar_component_clause,[],[f92])).
% 1.40/0.54  fof(f92,plain,(
% 1.40/0.54    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f8])).
% 1.40/0.54  fof(f565,plain,(
% 1.40/0.54    spl4_2 | spl4_3),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f556])).
% 1.40/0.54  fof(f556,plain,(
% 1.40/0.54    $false | (spl4_2 | spl4_3)),
% 1.40/0.54    inference(unit_resulting_resolution,[],[f32,f89,f33,f94,f461,f34,f72])).
% 1.40/0.54  fof(f72,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | o_0_0_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.40/0.54    inference(definition_unfolding,[],[f62,f36])).
% 1.40/0.54  fof(f62,plain,(
% 1.40/0.54    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relset_1(X0,X1,X3),X2) | k1_xboole_0 = X1 | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f29])).
% 1.40/0.54  fof(f105,plain,(
% 1.40/0.54    spl4_5),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f104])).
% 1.40/0.54  fof(f104,plain,(
% 1.40/0.54    $false | spl4_5),
% 1.40/0.54    inference(subsumption_resolution,[],[f32,f102])).
% 1.40/0.54  fof(f102,plain,(
% 1.40/0.54    ~v1_funct_1(sK3) | spl4_5),
% 1.40/0.54    inference(avatar_component_clause,[],[f100])).
% 1.40/0.54  fof(f100,plain,(
% 1.40/0.54    spl4_5 <=> v1_funct_1(sK3)),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.40/0.54  fof(f103,plain,(
% 1.40/0.54    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 1.40/0.54    inference(avatar_split_clause,[],[f30,f100,f96,f92])).
% 1.40/0.54  fof(f30,plain,(
% 1.40/0.54    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f90,plain,(
% 1.40/0.54    spl4_1 | ~spl4_2),
% 1.40/0.54    inference(avatar_split_clause,[],[f64,f87,f83])).
% 1.40/0.54  fof(f64,plain,(
% 1.40/0.54    o_0_0_xboole_0 != sK1 | o_0_0_xboole_0 = sK0),
% 1.40/0.54    inference(definition_unfolding,[],[f31,f36,f36])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  % SZS output end Proof for theBenchmark
% 1.40/0.54  % (26864)------------------------------
% 1.40/0.54  % (26864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (26864)Termination reason: Refutation
% 1.40/0.54  
% 1.40/0.54  % (26864)Memory used [KB]: 6652
% 1.40/0.54  % (26864)Time elapsed: 0.124 s
% 1.40/0.54  % (26864)------------------------------
% 1.40/0.54  % (26864)------------------------------
% 1.40/0.55  % (26850)Success in time 0.183 s
%------------------------------------------------------------------------------
