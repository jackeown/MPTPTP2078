%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:22 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 847 expanded)
%              Number of leaves         :   27 ( 218 expanded)
%              Depth                    :   22
%              Number of atoms          :  527 (4266 expanded)
%              Number of equality atoms :  117 ( 801 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f689,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f120,f129,f133,f202,f221,f317,f346,f478,f602,f634,f685])).

fof(f685,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f684])).

fof(f684,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f670,f102])).

fof(f102,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_3
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f670,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(superposition,[],[f181,f325])).

fof(f325,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl3_13
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f181,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f180,f157])).

fof(f157,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f153,f50])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f37])).

fof(f37,plain,
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

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f153,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f73,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f180,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f179,f149])).

fof(f149,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f148,f130])).

fof(f130,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f125,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f125,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f53,f48])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f148,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f147,f46])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f147,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f49])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f179,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f178,f152])).

fof(f152,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f151,f130])).

fof(f151,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f150,f46])).

fof(f150,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f61,f49])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f178,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f174,f119])).

fof(f119,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_5
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f174,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f134,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f134,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f121,f130])).

fof(f121,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f634,plain,
    ( ~ spl3_8
    | spl3_13 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | ~ spl3_8
    | spl3_13 ),
    inference(global_subsumption,[],[f234,f324])).

fof(f324,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f323])).

fof(f234,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f158,f197])).

fof(f197,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f195])).

fof(f195,plain,
    ( spl3_8
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f158,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f602,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f597,f499])).

fof(f499,plain,
    ( ! [X5] : v1_funct_2(k1_xboole_0,k1_xboole_0,X5)
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f418,f491])).

fof(f491,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f240,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f240,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f239,f108])).

fof(f108,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f62,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f239,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f138,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f138,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f75,f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f418,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X5) )
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f417,f159])).

fof(f159,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f74,f52])).

fof(f417,plain,
    ( ! [X5] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X5,k1_xboole_0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X5) )
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f416,f349])).

fof(f349,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f348,f84])).

fof(f348,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f220,f201])).

fof(f201,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f199])).

fof(f199,plain,
    ( spl3_9
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f220,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl3_11
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f416,plain,
    ( ! [X5] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X5)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X5,sK2) )
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f407,f349])).

fof(f407,plain,
    ( ! [X5] :
        ( v1_funct_2(sK2,k1_xboole_0,X5)
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X5,sK2) )
    | ~ spl3_9 ),
    inference(resolution,[],[f341,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f89,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f330,f84])).

fof(f330,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl3_9 ),
    inference(superposition,[],[f48,f201])).

fof(f597,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f387,f559])).

fof(f559,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(resolution,[],[f475,f54])).

fof(f475,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f474,f85])).

fof(f474,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f473,f201])).

fof(f473,plain,
    ( r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0)))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f459,f349])).

fof(f459,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))
    | ~ spl3_5 ),
    inference(resolution,[],[f181,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f387,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl3_2
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f363,f201])).

fof(f363,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0)
    | spl3_2
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(superposition,[],[f98,f349])).

fof(f98,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f478,plain,
    ( spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl3_3
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f476,f342])).

fof(f342,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl3_3
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f333,f85])).

fof(f333,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl3_3
    | ~ spl3_9 ),
    inference(superposition,[],[f102,f201])).

fof(f476,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f460,f85])).

fof(f460,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(superposition,[],[f181,f201])).

fof(f346,plain,
    ( ~ spl3_9
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl3_9
    | spl3_10 ),
    inference(subsumption_resolution,[],[f344,f123])).

fof(f123,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f68,f52])).

fof(f344,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_9
    | spl3_10 ),
    inference(forward_demodulation,[],[f337,f84])).

fof(f337,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | ~ spl3_9
    | spl3_10 ),
    inference(superposition,[],[f216,f201])).

fof(f216,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl3_10
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f317,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f315,f98])).

fof(f315,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(superposition,[],[f185,f234])).

fof(f185,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f184,f157])).

fof(f184,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f183,f149])).

fof(f183,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f182,f152])).

fof(f182,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f175,f119])).

fof(f175,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f134,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f221,plain,
    ( ~ spl3_10
    | spl3_11 ),
    inference(avatar_split_clause,[],[f211,f218,f214])).

fof(f211,plain,
    ( sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    inference(resolution,[],[f122,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f122,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f68,f48])).

fof(f202,plain,
    ( spl3_8
    | spl3_9 ),
    inference(avatar_split_clause,[],[f193,f199,f195])).

fof(f193,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f189,f47])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f189,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f133,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f131,f130])).

fof(f131,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f121,f94])).

fof(f94,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_1
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f129,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_4 ),
    inference(subsumption_resolution,[],[f127,f62])).

fof(f127,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f125,f115])).

fof(f115,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f120,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f111,f117,f113])).

fof(f111,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f103,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f51,f100,f96,f92])).

fof(f51,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:47:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (15151)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (15143)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (15163)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (15152)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.50  % (15167)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (15146)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (15148)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.16/0.51  % (15157)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.16/0.51  % (15155)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.16/0.51  % (15165)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.16/0.52  % (15158)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.16/0.52  % (15147)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.16/0.52  % (15166)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.16/0.52  % (15145)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.16/0.53  % (15149)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.16/0.53  % (15153)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.16/0.53  % (15150)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.16/0.53  % (15164)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.16/0.53  % (15148)Refutation not found, incomplete strategy% (15148)------------------------------
% 1.16/0.53  % (15148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (15148)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (15148)Memory used [KB]: 6396
% 1.16/0.53  % (15148)Time elapsed: 0.124 s
% 1.16/0.53  % (15148)------------------------------
% 1.16/0.53  % (15148)------------------------------
% 1.16/0.53  % (15160)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.16/0.53  % (15149)Refutation not found, incomplete strategy% (15149)------------------------------
% 1.16/0.53  % (15149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.16/0.53  % (15149)Termination reason: Refutation not found, incomplete strategy
% 1.16/0.53  
% 1.16/0.53  % (15149)Memory used [KB]: 10618
% 1.16/0.53  % (15149)Time elapsed: 0.085 s
% 1.16/0.53  % (15149)------------------------------
% 1.16/0.53  % (15149)------------------------------
% 1.16/0.53  % (15144)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.16/0.54  % (15156)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.39/0.54  % (15144)Refutation not found, incomplete strategy% (15144)------------------------------
% 1.39/0.54  % (15144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (15144)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (15144)Memory used [KB]: 10746
% 1.39/0.54  % (15144)Time elapsed: 0.126 s
% 1.39/0.54  % (15144)------------------------------
% 1.39/0.54  % (15144)------------------------------
% 1.39/0.54  % (15161)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.39/0.55  % (15162)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.39/0.55  % (15159)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.39/0.55  % (15154)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.39/0.55  % (15153)Refutation found. Thanks to Tanya!
% 1.39/0.55  % SZS status Theorem for theBenchmark
% 1.39/0.55  % SZS output start Proof for theBenchmark
% 1.39/0.55  fof(f689,plain,(
% 1.39/0.55    $false),
% 1.39/0.55    inference(avatar_sat_refutation,[],[f103,f120,f129,f133,f202,f221,f317,f346,f478,f602,f634,f685])).
% 1.39/0.55  fof(f685,plain,(
% 1.39/0.55    spl3_3 | ~spl3_5 | ~spl3_13),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f684])).
% 1.39/0.55  fof(f684,plain,(
% 1.39/0.55    $false | (spl3_3 | ~spl3_5 | ~spl3_13)),
% 1.39/0.55    inference(subsumption_resolution,[],[f670,f102])).
% 1.39/0.55  fof(f102,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl3_3),
% 1.39/0.55    inference(avatar_component_clause,[],[f100])).
% 1.39/0.55  fof(f100,plain,(
% 1.39/0.55    spl3_3 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.39/0.55  fof(f670,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl3_5 | ~spl3_13)),
% 1.39/0.55    inference(superposition,[],[f181,f325])).
% 1.39/0.55  fof(f325,plain,(
% 1.39/0.55    sK0 = k1_relat_1(sK2) | ~spl3_13),
% 1.39/0.55    inference(avatar_component_clause,[],[f323])).
% 1.39/0.55  fof(f323,plain,(
% 1.39/0.55    spl3_13 <=> sK0 = k1_relat_1(sK2)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.39/0.55  fof(f181,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~spl3_5),
% 1.39/0.55    inference(forward_demodulation,[],[f180,f157])).
% 1.39/0.55  fof(f157,plain,(
% 1.39/0.55    sK1 = k2_relat_1(sK2)),
% 1.39/0.55    inference(forward_demodulation,[],[f153,f50])).
% 1.39/0.55  fof(f50,plain,(
% 1.39/0.55    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f38,plain,(
% 1.39/0.55    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.39/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f37])).
% 1.39/0.55  fof(f37,plain,(
% 1.39/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & sK1 = k2_relset_1(sK0,sK1,sK2) & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.39/0.55    introduced(choice_axiom,[])).
% 1.39/0.55  fof(f22,plain,(
% 1.39/0.55    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.55    inference(flattening,[],[f21])).
% 1.39/0.55  fof(f21,plain,(
% 1.39/0.55    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.55    inference(ennf_transformation,[],[f18])).
% 1.39/0.55  fof(f18,negated_conjecture,(
% 1.39/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.39/0.55    inference(negated_conjecture,[],[f17])).
% 1.39/0.55  fof(f17,conjecture,(
% 1.39/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.39/0.55  fof(f153,plain,(
% 1.39/0.55    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f73,f48])).
% 1.39/0.55  fof(f48,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f73,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f32])).
% 1.39/0.55  fof(f32,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f14])).
% 1.39/0.55  fof(f14,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.39/0.55  fof(f180,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_5),
% 1.39/0.55    inference(forward_demodulation,[],[f179,f149])).
% 1.39/0.55  fof(f149,plain,(
% 1.39/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.39/0.55    inference(subsumption_resolution,[],[f148,f130])).
% 1.39/0.55  fof(f130,plain,(
% 1.39/0.55    v1_relat_1(sK2)),
% 1.39/0.55    inference(subsumption_resolution,[],[f125,f62])).
% 1.39/0.55  fof(f62,plain,(
% 1.39/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f9])).
% 1.39/0.55  fof(f9,axiom,(
% 1.39/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.55  fof(f125,plain,(
% 1.39/0.55    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.39/0.55    inference(resolution,[],[f53,f48])).
% 1.39/0.55  fof(f53,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f23])).
% 1.39/0.55  fof(f23,plain,(
% 1.39/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(ennf_transformation,[],[f7])).
% 1.39/0.55  fof(f7,axiom,(
% 1.39/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.39/0.55  fof(f148,plain,(
% 1.39/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.39/0.55    inference(subsumption_resolution,[],[f147,f46])).
% 1.39/0.55  fof(f46,plain,(
% 1.39/0.55    v1_funct_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f147,plain,(
% 1.39/0.55    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f60,f49])).
% 1.39/0.55  fof(f49,plain,(
% 1.39/0.55    v2_funct_1(sK2)),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f60,plain,(
% 1.39/0.55    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f30])).
% 1.39/0.55  fof(f30,plain,(
% 1.39/0.55    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f29])).
% 1.39/0.55  fof(f29,plain,(
% 1.39/0.55    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f11])).
% 1.39/0.55  fof(f11,axiom,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.39/0.55  fof(f179,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) | ~spl3_5),
% 1.39/0.55    inference(forward_demodulation,[],[f178,f152])).
% 1.39/0.55  fof(f152,plain,(
% 1.39/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.39/0.55    inference(subsumption_resolution,[],[f151,f130])).
% 1.39/0.55  fof(f151,plain,(
% 1.39/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.39/0.55    inference(subsumption_resolution,[],[f150,f46])).
% 1.39/0.55  fof(f150,plain,(
% 1.39/0.55    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f61,f49])).
% 1.39/0.55  fof(f61,plain,(
% 1.39/0.55    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f30])).
% 1.39/0.55  fof(f178,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~spl3_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f174,f119])).
% 1.39/0.55  fof(f119,plain,(
% 1.39/0.55    v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.39/0.55    inference(avatar_component_clause,[],[f117])).
% 1.39/0.55  fof(f117,plain,(
% 1.39/0.55    spl3_5 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.39/0.55  fof(f174,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.39/0.55    inference(resolution,[],[f134,f57])).
% 1.39/0.55  fof(f57,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f26,plain,(
% 1.39/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f25])).
% 1.39/0.55  fof(f25,plain,(
% 1.39/0.55    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f16])).
% 1.39/0.55  fof(f16,axiom,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.39/0.55  fof(f134,plain,(
% 1.39/0.55    v1_funct_1(k2_funct_1(sK2))),
% 1.39/0.55    inference(subsumption_resolution,[],[f121,f130])).
% 1.39/0.55  fof(f121,plain,(
% 1.39/0.55    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f59,f46])).
% 1.39/0.55  fof(f59,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f28])).
% 1.39/0.55  fof(f28,plain,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.55    inference(flattening,[],[f27])).
% 1.39/0.55  fof(f27,plain,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.55    inference(ennf_transformation,[],[f10])).
% 1.39/0.55  fof(f10,axiom,(
% 1.39/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.39/0.55  fof(f634,plain,(
% 1.39/0.55    ~spl3_8 | spl3_13),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f633])).
% 1.39/0.55  fof(f633,plain,(
% 1.39/0.55    $false | (~spl3_8 | spl3_13)),
% 1.39/0.55    inference(global_subsumption,[],[f234,f324])).
% 1.39/0.55  fof(f324,plain,(
% 1.39/0.55    sK0 != k1_relat_1(sK2) | spl3_13),
% 1.39/0.55    inference(avatar_component_clause,[],[f323])).
% 1.39/0.55  fof(f234,plain,(
% 1.39/0.55    sK0 = k1_relat_1(sK2) | ~spl3_8),
% 1.39/0.55    inference(superposition,[],[f158,f197])).
% 1.39/0.55  fof(f197,plain,(
% 1.39/0.55    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl3_8),
% 1.39/0.55    inference(avatar_component_clause,[],[f195])).
% 1.39/0.55  fof(f195,plain,(
% 1.39/0.55    spl3_8 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.39/0.55  fof(f158,plain,(
% 1.39/0.55    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.55    inference(resolution,[],[f74,f48])).
% 1.39/0.55  fof(f74,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f33])).
% 1.39/0.55  fof(f33,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f13])).
% 1.39/0.55  fof(f13,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.55  fof(f602,plain,(
% 1.39/0.55    spl3_2 | ~spl3_5 | ~spl3_9 | ~spl3_11),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f601])).
% 1.39/0.55  fof(f601,plain,(
% 1.39/0.55    $false | (spl3_2 | ~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(subsumption_resolution,[],[f597,f499])).
% 1.39/0.55  fof(f499,plain,(
% 1.39/0.55    ( ! [X5] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X5)) ) | (~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(subsumption_resolution,[],[f418,f491])).
% 1.39/0.55  fof(f491,plain,(
% 1.39/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(resolution,[],[f240,f54])).
% 1.39/0.55  fof(f54,plain,(
% 1.39/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f24])).
% 1.39/0.55  fof(f24,plain,(
% 1.39/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.39/0.55    inference(ennf_transformation,[],[f2])).
% 1.39/0.55  fof(f2,axiom,(
% 1.39/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.39/0.55  fof(f240,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 1.39/0.55    inference(subsumption_resolution,[],[f239,f108])).
% 1.39/0.55  fof(f108,plain,(
% 1.39/0.55    v1_relat_1(k1_xboole_0)),
% 1.39/0.55    inference(superposition,[],[f62,f84])).
% 1.39/0.55  fof(f84,plain,(
% 1.39/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.55    inference(equality_resolution,[],[f72])).
% 1.39/0.55  fof(f72,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f44,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.55    inference(flattening,[],[f43])).
% 1.39/0.55  fof(f43,plain,(
% 1.39/0.55    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.55    inference(nnf_transformation,[],[f3])).
% 1.39/0.55  fof(f3,axiom,(
% 1.39/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.55  fof(f239,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.39/0.55    inference(resolution,[],[f138,f63])).
% 1.39/0.55  fof(f63,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f39])).
% 1.39/0.55  fof(f39,plain,(
% 1.39/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f31])).
% 1.39/0.55  fof(f31,plain,(
% 1.39/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.39/0.55    inference(ennf_transformation,[],[f8])).
% 1.39/0.55  fof(f8,axiom,(
% 1.39/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.39/0.55  fof(f138,plain,(
% 1.39/0.55    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(resolution,[],[f75,f52])).
% 1.39/0.55  fof(f52,plain,(
% 1.39/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f4])).
% 1.39/0.55  fof(f4,axiom,(
% 1.39/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.39/0.55  fof(f75,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f34])).
% 1.39/0.55  fof(f34,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f19])).
% 1.39/0.55  fof(f19,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.39/0.55    inference(pure_predicate_removal,[],[f12])).
% 1.39/0.55  fof(f12,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.39/0.55  fof(f418,plain,(
% 1.39/0.55    ( ! [X5] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X5)) ) | (~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f417,f159])).
% 1.39/0.55  fof(f159,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 1.39/0.55    inference(resolution,[],[f74,f52])).
% 1.39/0.55  fof(f417,plain,(
% 1.39/0.55    ( ! [X5] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X5,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X5)) ) | (~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f416,f349])).
% 1.39/0.55  fof(f349,plain,(
% 1.39/0.55    k1_xboole_0 = sK2 | (~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f348,f84])).
% 1.39/0.55  fof(f348,plain,(
% 1.39/0.55    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | (~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f220,f201])).
% 1.39/0.55  fof(f201,plain,(
% 1.39/0.55    k1_xboole_0 = sK1 | ~spl3_9),
% 1.39/0.55    inference(avatar_component_clause,[],[f199])).
% 1.39/0.55  fof(f199,plain,(
% 1.39/0.55    spl3_9 <=> k1_xboole_0 = sK1),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.39/0.55  fof(f220,plain,(
% 1.39/0.55    sK2 = k2_zfmisc_1(sK0,sK1) | ~spl3_11),
% 1.39/0.55    inference(avatar_component_clause,[],[f218])).
% 1.39/0.55  fof(f218,plain,(
% 1.39/0.55    spl3_11 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.39/0.55  fof(f416,plain,(
% 1.39/0.55    ( ! [X5] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X5) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X5,sK2)) ) | (~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f407,f349])).
% 1.39/0.55  fof(f407,plain,(
% 1.39/0.55    ( ! [X5] : (v1_funct_2(sK2,k1_xboole_0,X5) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X5,sK2)) ) | ~spl3_9),
% 1.39/0.55    inference(resolution,[],[f341,f106])).
% 1.39/0.55  fof(f106,plain,(
% 1.39/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 1.39/0.55    inference(forward_demodulation,[],[f89,f85])).
% 1.39/0.55  fof(f85,plain,(
% 1.39/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.39/0.55    inference(equality_resolution,[],[f71])).
% 1.39/0.55  fof(f71,plain,(
% 1.39/0.55    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f44])).
% 1.39/0.55  fof(f89,plain,(
% 1.39/0.55    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.39/0.55    inference(equality_resolution,[],[f79])).
% 1.39/0.55  fof(f79,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.55    inference(cnf_transformation,[],[f45])).
% 1.39/0.55  fof(f45,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(nnf_transformation,[],[f36])).
% 1.39/0.55  fof(f36,plain,(
% 1.39/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(flattening,[],[f35])).
% 1.39/0.55  fof(f35,plain,(
% 1.39/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.55    inference(ennf_transformation,[],[f15])).
% 1.39/0.55  fof(f15,axiom,(
% 1.39/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.55  fof(f341,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_9),
% 1.39/0.55    inference(forward_demodulation,[],[f330,f84])).
% 1.39/0.55  fof(f330,plain,(
% 1.39/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl3_9),
% 1.39/0.55    inference(superposition,[],[f48,f201])).
% 1.39/0.55  fof(f597,plain,(
% 1.39/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl3_2 | ~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(superposition,[],[f387,f559])).
% 1.39/0.55  fof(f559,plain,(
% 1.39/0.55    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(resolution,[],[f475,f54])).
% 1.39/0.55  fof(f475,plain,(
% 1.39/0.55    r1_tarski(k2_funct_1(k1_xboole_0),k1_xboole_0) | (~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f474,f85])).
% 1.39/0.55  fof(f474,plain,(
% 1.39/0.55    r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0))) | (~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f473,f201])).
% 1.39/0.55  fof(f473,plain,(
% 1.39/0.55    r1_tarski(k2_funct_1(k1_xboole_0),k2_zfmisc_1(sK1,k1_relat_1(k1_xboole_0))) | (~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f459,f349])).
% 1.39/0.55  fof(f459,plain,(
% 1.39/0.55    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) | ~spl3_5),
% 1.39/0.55    inference(resolution,[],[f181,f68])).
% 1.39/0.55  fof(f68,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f42])).
% 1.39/0.55  fof(f42,plain,(
% 1.39/0.55    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.39/0.55    inference(nnf_transformation,[],[f5])).
% 1.39/0.55  fof(f5,axiom,(
% 1.39/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.39/0.55  fof(f387,plain,(
% 1.39/0.55    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl3_2 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(forward_demodulation,[],[f363,f201])).
% 1.39/0.55  fof(f363,plain,(
% 1.39/0.55    ~v1_funct_2(k2_funct_1(k1_xboole_0),sK1,sK0) | (spl3_2 | ~spl3_9 | ~spl3_11)),
% 1.39/0.55    inference(superposition,[],[f98,f349])).
% 1.39/0.55  fof(f98,plain,(
% 1.39/0.55    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl3_2),
% 1.39/0.55    inference(avatar_component_clause,[],[f96])).
% 1.39/0.55  fof(f96,plain,(
% 1.39/0.55    spl3_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.39/0.55  fof(f478,plain,(
% 1.39/0.55    spl3_3 | ~spl3_5 | ~spl3_9),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f477])).
% 1.39/0.55  fof(f477,plain,(
% 1.39/0.55    $false | (spl3_3 | ~spl3_5 | ~spl3_9)),
% 1.39/0.55    inference(subsumption_resolution,[],[f476,f342])).
% 1.39/0.55  fof(f342,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl3_3 | ~spl3_9)),
% 1.39/0.55    inference(forward_demodulation,[],[f333,f85])).
% 1.39/0.55  fof(f333,plain,(
% 1.39/0.55    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl3_3 | ~spl3_9)),
% 1.39/0.55    inference(superposition,[],[f102,f201])).
% 1.39/0.55  fof(f476,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (~spl3_5 | ~spl3_9)),
% 1.39/0.55    inference(forward_demodulation,[],[f460,f85])).
% 1.39/0.55  fof(f460,plain,(
% 1.39/0.55    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | (~spl3_5 | ~spl3_9)),
% 1.39/0.55    inference(superposition,[],[f181,f201])).
% 1.39/0.55  fof(f346,plain,(
% 1.39/0.55    ~spl3_9 | spl3_10),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f345])).
% 1.39/0.55  fof(f345,plain,(
% 1.39/0.55    $false | (~spl3_9 | spl3_10)),
% 1.39/0.55    inference(subsumption_resolution,[],[f344,f123])).
% 1.39/0.55  fof(f123,plain,(
% 1.39/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.39/0.55    inference(resolution,[],[f68,f52])).
% 1.39/0.55  fof(f344,plain,(
% 1.39/0.55    ~r1_tarski(k1_xboole_0,sK2) | (~spl3_9 | spl3_10)),
% 1.39/0.55    inference(forward_demodulation,[],[f337,f84])).
% 1.39/0.55  fof(f337,plain,(
% 1.39/0.55    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | (~spl3_9 | spl3_10)),
% 1.39/0.55    inference(superposition,[],[f216,f201])).
% 1.39/0.55  fof(f216,plain,(
% 1.39/0.55    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl3_10),
% 1.39/0.55    inference(avatar_component_clause,[],[f214])).
% 1.39/0.55  fof(f214,plain,(
% 1.39/0.55    spl3_10 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.39/0.55  fof(f317,plain,(
% 1.39/0.55    spl3_2 | ~spl3_5 | ~spl3_8),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f316])).
% 1.39/0.55  fof(f316,plain,(
% 1.39/0.55    $false | (spl3_2 | ~spl3_5 | ~spl3_8)),
% 1.39/0.55    inference(subsumption_resolution,[],[f315,f98])).
% 1.39/0.55  fof(f315,plain,(
% 1.39/0.55    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl3_5 | ~spl3_8)),
% 1.39/0.55    inference(superposition,[],[f185,f234])).
% 1.39/0.55  fof(f185,plain,(
% 1.39/0.55    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl3_5),
% 1.39/0.55    inference(forward_demodulation,[],[f184,f157])).
% 1.39/0.55  fof(f184,plain,(
% 1.39/0.55    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_5),
% 1.39/0.55    inference(forward_demodulation,[],[f183,f149])).
% 1.39/0.55  fof(f183,plain,(
% 1.39/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) | ~spl3_5),
% 1.39/0.55    inference(forward_demodulation,[],[f182,f152])).
% 1.39/0.55  fof(f182,plain,(
% 1.39/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~spl3_5),
% 1.39/0.55    inference(subsumption_resolution,[],[f175,f119])).
% 1.39/0.55  fof(f175,plain,(
% 1.39/0.55    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2))),
% 1.39/0.55    inference(resolution,[],[f134,f56])).
% 1.39/0.55  fof(f56,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f26])).
% 1.39/0.55  fof(f221,plain,(
% 1.39/0.55    ~spl3_10 | spl3_11),
% 1.39/0.55    inference(avatar_split_clause,[],[f211,f218,f214])).
% 1.39/0.55  fof(f211,plain,(
% 1.39/0.55    sK2 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 1.39/0.55    inference(resolution,[],[f122,f67])).
% 1.39/0.55  fof(f67,plain,(
% 1.39/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.39/0.55    inference(cnf_transformation,[],[f41])).
% 1.39/0.55  fof(f41,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(flattening,[],[f40])).
% 1.39/0.55  fof(f40,plain,(
% 1.39/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.39/0.55    inference(nnf_transformation,[],[f1])).
% 1.39/0.55  fof(f1,axiom,(
% 1.39/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.39/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.39/0.55  fof(f122,plain,(
% 1.39/0.55    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.55    inference(resolution,[],[f68,f48])).
% 1.39/0.55  fof(f202,plain,(
% 1.39/0.55    spl3_8 | spl3_9),
% 1.39/0.55    inference(avatar_split_clause,[],[f193,f199,f195])).
% 1.39/0.55  fof(f193,plain,(
% 1.39/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.55    inference(subsumption_resolution,[],[f189,f47])).
% 1.39/0.55  fof(f47,plain,(
% 1.39/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.55    inference(cnf_transformation,[],[f38])).
% 1.39/0.55  fof(f189,plain,(
% 1.39/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.55    inference(resolution,[],[f76,f48])).
% 1.39/0.55  fof(f76,plain,(
% 1.39/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.39/0.55    inference(cnf_transformation,[],[f45])).
% 1.39/0.55  fof(f133,plain,(
% 1.39/0.55    spl3_1),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f132])).
% 1.39/0.55  fof(f132,plain,(
% 1.39/0.55    $false | spl3_1),
% 1.39/0.55    inference(subsumption_resolution,[],[f131,f130])).
% 1.39/0.55  fof(f131,plain,(
% 1.39/0.55    ~v1_relat_1(sK2) | spl3_1),
% 1.39/0.55    inference(subsumption_resolution,[],[f121,f94])).
% 1.39/0.55  fof(f94,plain,(
% 1.39/0.55    ~v1_funct_1(k2_funct_1(sK2)) | spl3_1),
% 1.39/0.55    inference(avatar_component_clause,[],[f92])).
% 1.39/0.55  fof(f92,plain,(
% 1.39/0.55    spl3_1 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.39/0.55  fof(f129,plain,(
% 1.39/0.55    spl3_4),
% 1.39/0.55    inference(avatar_contradiction_clause,[],[f128])).
% 1.39/0.55  fof(f128,plain,(
% 1.39/0.55    $false | spl3_4),
% 1.39/0.55    inference(subsumption_resolution,[],[f127,f62])).
% 1.39/0.55  fof(f127,plain,(
% 1.39/0.55    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl3_4),
% 1.39/0.55    inference(subsumption_resolution,[],[f125,f115])).
% 1.39/0.55  fof(f115,plain,(
% 1.39/0.55    ~v1_relat_1(sK2) | spl3_4),
% 1.39/0.55    inference(avatar_component_clause,[],[f113])).
% 1.39/0.55  fof(f113,plain,(
% 1.39/0.55    spl3_4 <=> v1_relat_1(sK2)),
% 1.39/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.39/0.55  fof(f120,plain,(
% 1.39/0.55    ~spl3_4 | spl3_5),
% 1.39/0.55    inference(avatar_split_clause,[],[f111,f117,f113])).
% 1.39/0.55  fof(f111,plain,(
% 1.39/0.55    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.39/0.55    inference(resolution,[],[f58,f46])).
% 1.39/0.55  fof(f58,plain,(
% 1.39/0.55    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f28])).
% 1.39/0.56  fof(f103,plain,(
% 1.39/0.56    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.39/0.56    inference(avatar_split_clause,[],[f51,f100,f96,f92])).
% 1.39/0.56  fof(f51,plain,(
% 1.39/0.56    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.39/0.56    inference(cnf_transformation,[],[f38])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (15153)------------------------------
% 1.39/0.56  % (15153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (15153)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (15153)Memory used [KB]: 11001
% 1.39/0.56  % (15153)Time elapsed: 0.144 s
% 1.39/0.56  % (15153)------------------------------
% 1.39/0.56  % (15153)------------------------------
% 1.39/0.56  % (15168)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.39/0.56  % (15142)Success in time 0.189 s
%------------------------------------------------------------------------------
