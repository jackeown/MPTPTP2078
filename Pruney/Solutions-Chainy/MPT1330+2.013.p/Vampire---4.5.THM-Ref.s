%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 417 expanded)
%              Number of leaves         :   26 ( 145 expanded)
%              Depth                    :   15
%              Number of atoms          :  388 (2363 expanded)
%              Number of equality atoms :  134 ( 937 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f207,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f150,f155,f161,f176,f206])).

fof(f206,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f205])).

fof(f205,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f204,f103])).

fof(f103,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f83,f79])).

fof(f79,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f53,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f53,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f204,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_5 ),
    inference(forward_demodulation,[],[f188,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_1 ),
    inference(resolution,[],[f186,f162])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f119,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k8_relset_1(X0,X1,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f131,f55])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f131,plain,(
    ! [X2,X0,X1] : k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2) ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f119,plain,(
    ! [X0] :
      ( k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f66,f79])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f186,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f181,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f181,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_1 ),
    inference(backward_demodulation,[],[f110,f93])).

fof(f93,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f110,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f107,f105])).

fof(f105,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    & ( k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 != k2_struct_0(sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
                & ( k1_xboole_0 = k2_struct_0(X0)
                  | k1_xboole_0 != k2_struct_0(X1) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(sK0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1))
            & ( k1_xboole_0 = k2_struct_0(sK0)
              | k1_xboole_0 != k2_struct_0(X1) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
          & ( k1_xboole_0 = k2_struct_0(sK0)
            | k1_xboole_0 != k2_struct_0(sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1))
        & ( k1_xboole_0 = k2_struct_0(sK0)
          | k1_xboole_0 != k2_struct_0(sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
      & ( k1_xboole_0 = k2_struct_0(sK0)
        | k1_xboole_0 != k2_struct_0(sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f50,f104])).

fof(f104,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f61,f46])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f188,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ spl3_2
    | spl3_5 ),
    inference(backward_demodulation,[],[f149,f98])).

fof(f98,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f149,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl3_5
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f176,plain,
    ( spl3_1
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f175])).

fof(f175,plain,
    ( $false
    | spl3_1
    | spl3_5 ),
    inference(subsumption_resolution,[],[f174,f149])).

fof(f174,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f173,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f173,plain,
    ( ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f172,f94])).

fof(f94,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f172,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f171,f110])).

fof(f171,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(resolution,[],[f170,f109])).

fof(f109,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f108,f105])).

fof(f108,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f49,f104])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X1,X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | k1_xboole_0 = X0
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X2 ) ),
    inference(subsumption_resolution,[],[f169,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X2
      | ~ v4_relat_1(X1,X2) ) ),
    inference(subsumption_resolution,[],[f168,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X2
      | ~ v4_relat_1(X1,X2)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f89,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f161,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f156,f110])).

fof(f156,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_4 ),
    inference(resolution,[],[f145,f72])).

fof(f145,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f155,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f151,f110])).

fof(f151,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_struct_0(sK1))))
    | spl3_3 ),
    inference(resolution,[],[f141,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f112,f72])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f74,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f141,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_3
  <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f150,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f137,f147,f143,f139])).

fof(f137,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    inference(superposition,[],[f136,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(forward_demodulation,[],[f125,f83])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1)))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(subsumption_resolution,[],[f124,f81])).

fof(f81,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1)))
      | ~ v1_relat_1(k6_partfun1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1)))
      | ~ v1_relat_1(k6_partfun1(X1))
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X0),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f62,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_partfun1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f56])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f136,plain,(
    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) ),
    inference(superposition,[],[f111,f132])).

fof(f132,plain,(
    ! [X3] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3) ),
    inference(resolution,[],[f78,f110])).

fof(f111,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f106,f105])).

fof(f106,plain,(
    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f52,f104])).

fof(f52,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

% (27095)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f99,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f51,f96,f92])).

fof(f51,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:44:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (27088)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (27091)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.50  % (27098)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.51  % (27106)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (27111)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (27100)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (27091)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f207,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f99,f150,f155,f161,f176,f206])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2 | spl3_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f205])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    $false | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f204,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(superposition,[],[f83,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 0.21/0.52    inference(definition_unfolding,[],[f53,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 0.21/0.52    inference(definition_unfolding,[],[f59,f56])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl3_1 | ~spl3_2 | spl3_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f188,f191])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_1),
% 0.21/0.52    inference(resolution,[],[f186,f162])).
% 0.21/0.52  fof(f162,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(backward_demodulation,[],[f119,f135])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = k8_relset_1(X0,X1,k1_xboole_0,X2)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f131,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,k1_xboole_0,X2) = k10_relat_1(k1_xboole_0,X2)) )),
% 0.21/0.52    inference(resolution,[],[f78,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    ( ! [X0] : (k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,X0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.52    inference(superposition,[],[f66,f79])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl3_1),
% 0.21/0.52    inference(forward_demodulation,[],[f181,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(flattening,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_1),
% 0.21/0.52    inference(backward_demodulation,[],[f110,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl3_1 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.52    inference(forward_demodulation,[],[f107,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.52    inference(resolution,[],[f61,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    l1_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ((k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f40,f39,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ? [X2] : (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) & (k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f19])).
% 0.21/0.52  fof(f19,conjecture,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(backward_demodulation,[],[f50,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.52    inference(resolution,[],[f61,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    l1_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    k1_xboole_0 != k1_relat_1(sK2) | (~spl3_2 | spl3_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f149,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl3_2 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl3_5 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl3_1 | spl3_5),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f175])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    $false | (spl3_1 | spl3_5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f174,f149])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | spl3_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f173,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | spl3_1),
% 0.21/0.52    inference(subsumption_resolution,[],[f172,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k1_xboole_0 != k2_struct_0(sK1) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f171,f110])).
% 0.21/0.52  fof(f171,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f170,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.52    inference(forward_demodulation,[],[f108,f105])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f49,f104])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_funct_2(X1,X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0 | ~v1_funct_1(X1) | k1_relat_1(X1) = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f169,f73])).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f169,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | k1_relat_1(X1) = X2 | ~v4_relat_1(X1,X2)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f168,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | k1_relat_1(X1) = X2 | ~v4_relat_1(X1,X2) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(resolution,[],[f89,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    $false | spl3_4),
% 0.21/0.52    inference(resolution,[],[f156,f110])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_4),
% 0.21/0.52    inference(resolution,[],[f145,f72])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl3_4 <=> v1_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f155,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    $false | spl3_3),
% 0.21/0.52    inference(resolution,[],[f151,f110])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_struct_0(sK1))))) ) | spl3_3),
% 0.21/0.52    inference(resolution,[],[f141,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f112,f72])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f74,f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl3_3 <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ~spl3_3 | ~spl3_4 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f147,f143,f139])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.21/0.52    inference(superposition,[],[f136,f126])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f125,f83])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f124,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f57,f56])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1))) | ~v1_relat_1(k6_partfun1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_partfun1(X1))) | ~v1_relat_1(k6_partfun1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(superposition,[],[f62,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_partfun1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f63,f56])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.21/0.52    inference(superposition,[],[f111,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X3] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X3) = k10_relat_1(sK2,X3)) )),
% 0.21/0.52    inference(resolution,[],[f78,f110])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.52    inference(forward_demodulation,[],[f106,f105])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.52    inference(backward_demodulation,[],[f52,f104])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  % (27095)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    ~spl3_1 | spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f96,f92])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 != k2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (27091)------------------------------
% 0.21/0.52  % (27091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27091)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (27091)Memory used [KB]: 10874
% 0.21/0.52  % (27091)Time elapsed: 0.091 s
% 0.21/0.52  % (27091)------------------------------
% 0.21/0.52  % (27091)------------------------------
% 0.21/0.52  % (27103)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (27097)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (27103)Refutation not found, incomplete strategy% (27103)------------------------------
% 0.21/0.52  % (27103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (27103)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (27103)Memory used [KB]: 6140
% 0.21/0.52  % (27103)Time elapsed: 0.003 s
% 0.21/0.52  % (27103)------------------------------
% 0.21/0.52  % (27103)------------------------------
% 0.21/0.52  % (27087)Success in time 0.158 s
%------------------------------------------------------------------------------
