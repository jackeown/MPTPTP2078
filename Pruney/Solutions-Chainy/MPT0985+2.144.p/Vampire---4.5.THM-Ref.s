%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:22 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 472 expanded)
%              Number of leaves         :   17 ( 130 expanded)
%              Depth                    :   13
%              Number of atoms          :  273 (2506 expanded)
%              Number of equality atoms :   27 ( 300 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f446,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f75,f258,f260,f287,f300,f445])).

fof(f445,plain,
    ( spl3_3
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f442])).

fof(f442,plain,
    ( $false
    | spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f127,f164,f286])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(sK2),X0)
        | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl3_11
  <=> ! [X0] :
        ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f164,plain,
    ( ~ m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(backward_demodulation,[],[f60,f160])).

fof(f160,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f76,f28,f31,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f31,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f28,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    v1_relat_1(sK2) ),
    inference(global_subsumption,[],[f72])).

fof(f72,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f40,f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f60,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f127,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f76,f125,f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f125,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(unit_resulting_resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f300,plain,
    ( spl3_2
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl3_2
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f127,f163,f268])).

fof(f268,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),sK1,X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f257,f267])).

fof(f267,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f265,f32])).

fof(f32,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f265,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f257,plain,
    ( ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl3_10
  <=> ! [X0] :
        ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0)
        | ~ r1_tarski(k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f163,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f56,f160])).

fof(f56,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f287,plain,
    ( ~ spl3_9
    | spl3_11 ),
    inference(avatar_split_clause,[],[f283,f285,f252])).

fof(f252,plain,
    ( spl3_9
  <=> v1_funct_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f283,plain,(
    ! [X0] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_funct_1(k4_relat_1(sK2)) ) ),
    inference(global_subsumption,[],[f165,f282])).

fof(f282,plain,(
    ! [X0] :
      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_funct_1(k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f279,f272])).

fof(f272,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f78,f267])).

fof(f78,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f76,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f279,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X0)))
      | ~ v1_funct_1(k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(superposition,[],[f45,f77])).

fof(f77,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f76,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

fof(f165,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f80,f160])).

fof(f80,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f28,f76,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f260,plain,
    ( ~ spl3_1
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f259])).

fof(f259,plain,
    ( $false
    | ~ spl3_1
    | spl3_9 ),
    inference(subsumption_resolution,[],[f162,f254])).

fof(f254,plain,
    ( ~ v1_funct_1(k4_relat_1(sK2))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f252])).

fof(f162,plain,
    ( v1_funct_1(k4_relat_1(sK2))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f51,f160])).

fof(f51,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f258,plain,
    ( ~ spl3_9
    | spl3_10 ),
    inference(avatar_split_clause,[],[f250,f256,f252])).

fof(f250,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_funct_1(k4_relat_1(sK2)) ) ),
    inference(global_subsumption,[],[f165,f249])).

fof(f249,plain,(
    ! [X0] :
      ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0)
      | ~ r1_tarski(k1_relat_1(sK2),X0)
      | ~ v1_funct_1(k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(forward_demodulation,[],[f247,f78])).

% (27135)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f247,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK2),X0)
      | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0)
      | ~ v1_funct_1(k4_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(superposition,[],[f44,f77])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f62,f40,f30,f36])).

fof(f62,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f28,f52,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f61,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f33,f58,f54,f50])).

fof(f33,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:27:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (27131)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.19/0.45  % (27139)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.19/0.46  % (27139)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % (27125)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f446,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f61,f75,f258,f260,f287,f300,f445])).
% 0.19/0.48  fof(f445,plain,(
% 0.19/0.48    spl3_3 | ~spl3_11),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f442])).
% 0.19/0.48  fof(f442,plain,(
% 0.19/0.48    $false | (spl3_3 | ~spl3_11)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f127,f164,f286])).
% 0.19/0.48  fof(f286,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl3_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f285])).
% 0.19/0.48  fof(f285,plain,(
% 0.19/0.48    spl3_11 <=> ! [X0] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.48  fof(f164,plain,(
% 0.19/0.48    ~m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.19/0.48    inference(backward_demodulation,[],[f60,f160])).
% 0.19/0.48  fof(f160,plain,(
% 0.19/0.48    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f76,f28,f31,f39])).
% 0.19/0.48  fof(f39,plain,(
% 0.19/0.48    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f19])).
% 0.19/0.48  fof(f19,plain,(
% 0.19/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f5])).
% 0.19/0.48  fof(f5,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.19/0.48  fof(f31,plain,(
% 0.19/0.48    v2_funct_1(sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.19/0.48    inference(flattening,[],[f12])).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.19/0.48    inference(ennf_transformation,[],[f11])).
% 0.19/0.48  fof(f11,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.48    inference(negated_conjecture,[],[f10])).
% 0.19/0.48  fof(f10,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.19/0.48  fof(f28,plain,(
% 0.19/0.48    v1_funct_1(sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f76,plain,(
% 0.19/0.48    v1_relat_1(sK2)),
% 0.19/0.48    inference(global_subsumption,[],[f72])).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    v1_relat_1(sK2)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f40,f30,f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.19/0.48  fof(f30,plain,(
% 0.19/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f40,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.19/0.48  fof(f60,plain,(
% 0.19/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f58])).
% 0.19/0.48  fof(f58,plain,(
% 0.19/0.48    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.48  fof(f127,plain,(
% 0.19/0.48    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f76,f125,f41])).
% 0.19/0.48  fof(f41,plain,(
% 0.19/0.48    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f27])).
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(nnf_transformation,[],[f20])).
% 0.19/0.48  fof(f20,plain,(
% 0.19/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.19/0.48  fof(f125,plain,(
% 0.19/0.48    v4_relat_1(sK2,sK0)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f30,f47])).
% 0.19/0.48  fof(f47,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.19/0.48  fof(f300,plain,(
% 0.19/0.48    spl3_2 | ~spl3_10),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f298])).
% 0.19/0.48  fof(f298,plain,(
% 0.19/0.48    $false | (spl3_2 | ~spl3_10)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f127,f163,f268])).
% 0.19/0.48  fof(f268,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),sK1,X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_10),
% 0.19/0.48    inference(backward_demodulation,[],[f257,f267])).
% 0.19/0.48  fof(f267,plain,(
% 0.19/0.48    sK1 = k2_relat_1(sK2)),
% 0.19/0.48    inference(forward_demodulation,[],[f265,f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f265,plain,(
% 0.19/0.48    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f30,f46])).
% 0.19/0.48  fof(f46,plain,(
% 0.19/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.19/0.48  fof(f257,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0) | ~r1_tarski(k1_relat_1(sK2),X0)) ) | ~spl3_10),
% 0.19/0.48    inference(avatar_component_clause,[],[f256])).
% 0.19/0.48  fof(f256,plain,(
% 0.19/0.48    spl3_10 <=> ! [X0] : (v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0) | ~r1_tarski(k1_relat_1(sK2),X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.48  fof(f163,plain,(
% 0.19/0.48    ~v1_funct_2(k4_relat_1(sK2),sK1,sK0) | spl3_2),
% 0.19/0.48    inference(backward_demodulation,[],[f56,f160])).
% 0.19/0.48  fof(f56,plain,(
% 0.19/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f54])).
% 0.19/0.48  fof(f54,plain,(
% 0.19/0.48    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.48  fof(f287,plain,(
% 0.19/0.48    ~spl3_9 | spl3_11),
% 0.19/0.48    inference(avatar_split_clause,[],[f283,f285,f252])).
% 0.19/0.48  fof(f252,plain,(
% 0.19/0.48    spl3_9 <=> v1_funct_1(k4_relat_1(sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.48  fof(f283,plain,(
% 0.19/0.48    ( ! [X0] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(k4_relat_1(sK2))) )),
% 0.19/0.48    inference(global_subsumption,[],[f165,f282])).
% 0.19/0.48  fof(f282,plain,(
% 0.19/0.48    ( ! [X0] : (m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.19/0.48    inference(forward_demodulation,[],[f279,f272])).
% 0.19/0.48  fof(f272,plain,(
% 0.19/0.48    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 0.19/0.48    inference(backward_demodulation,[],[f78,f267])).
% 0.19/0.48  fof(f78,plain,(
% 0.19/0.48    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f76,f34])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.19/0.48  fof(f279,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),X0))) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.19/0.48    inference(superposition,[],[f45,f77])).
% 0.19/0.48  fof(f77,plain,(
% 0.19/0.48    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f76,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.19/0.48    inference(cnf_transformation,[],[f14])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.48    inference(flattening,[],[f21])).
% 0.19/0.48  fof(f21,plain,(
% 0.19/0.48    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,axiom,(
% 0.19/0.48    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).
% 0.19/0.48  fof(f165,plain,(
% 0.19/0.48    v1_relat_1(k4_relat_1(sK2))),
% 0.19/0.48    inference(backward_demodulation,[],[f80,f160])).
% 0.19/0.48  fof(f80,plain,(
% 0.19/0.48    v1_relat_1(k2_funct_1(sK2))),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f28,f76,f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.19/0.48    inference(flattening,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,axiom,(
% 0.19/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.19/0.48  fof(f260,plain,(
% 0.19/0.48    ~spl3_1 | spl3_9),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f259])).
% 0.19/0.48  fof(f259,plain,(
% 0.19/0.48    $false | (~spl3_1 | spl3_9)),
% 0.19/0.48    inference(subsumption_resolution,[],[f162,f254])).
% 0.19/0.48  fof(f254,plain,(
% 0.19/0.48    ~v1_funct_1(k4_relat_1(sK2)) | spl3_9),
% 0.19/0.48    inference(avatar_component_clause,[],[f252])).
% 0.19/0.48  fof(f162,plain,(
% 0.19/0.48    v1_funct_1(k4_relat_1(sK2)) | ~spl3_1),
% 0.19/0.48    inference(backward_demodulation,[],[f51,f160])).
% 0.19/0.48  fof(f51,plain,(
% 0.19/0.48    v1_funct_1(k2_funct_1(sK2)) | ~spl3_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f50])).
% 0.19/0.48  fof(f50,plain,(
% 0.19/0.48    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.48  fof(f258,plain,(
% 0.19/0.48    ~spl3_9 | spl3_10),
% 0.19/0.48    inference(avatar_split_clause,[],[f250,f256,f252])).
% 0.19/0.48  fof(f250,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(k4_relat_1(sK2))) )),
% 0.19/0.48    inference(global_subsumption,[],[f165,f249])).
% 0.19/0.48  fof(f249,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),X0) | ~r1_tarski(k1_relat_1(sK2),X0) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.19/0.48    inference(forward_demodulation,[],[f247,f78])).
% 0.19/0.48  % (27135)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.19/0.48  fof(f247,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(k1_relat_1(sK2),X0) | v1_funct_2(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)),X0) | ~v1_funct_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 0.19/0.48    inference(superposition,[],[f44,f77])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f22])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    spl3_1),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    $false | spl3_1),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f62,f40,f30,f36])).
% 0.19/0.48  fof(f62,plain,(
% 0.19/0.48    ~v1_relat_1(sK2) | spl3_1),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f28,f52,f38])).
% 0.19/0.48  fof(f38,plain,(
% 0.19/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f17])).
% 0.19/0.48  fof(f52,plain,(
% 0.19/0.48    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f50])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 0.19/0.48    inference(avatar_split_clause,[],[f33,f58,f54,f50])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (27139)------------------------------
% 0.19/0.48  % (27139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (27139)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (27139)Memory used [KB]: 10874
% 0.19/0.48  % (27139)Time elapsed: 0.081 s
% 0.19/0.48  % (27139)------------------------------
% 0.19/0.48  % (27139)------------------------------
% 0.19/0.48  % (27141)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.19/0.48  % (27119)Success in time 0.129 s
%------------------------------------------------------------------------------
