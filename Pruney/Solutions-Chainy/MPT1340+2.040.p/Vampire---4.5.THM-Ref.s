%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 448 expanded)
%              Number of leaves         :   44 ( 197 expanded)
%              Depth                    :   11
%              Number of atoms          :  739 (2345 expanded)
%              Number of equality atoms :  115 ( 348 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f985,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f124,f128,f182,f203,f216,f240,f281,f288,f324,f330,f350,f357,f367,f411,f434,f514,f518,f598,f603,f762,f799,f805,f912,f973,f984])).

fof(f984,plain,(
    ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f983])).

fof(f983,plain,
    ( $false
    | ~ spl3_14 ),
    inference(resolution,[],[f198,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f43,f42,f41])).

fof(f41,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).

fof(f198,plain,
    ( v2_struct_0(sK1)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_14
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f973,plain,
    ( spl3_15
    | ~ spl3_91 ),
    inference(avatar_contradiction_clause,[],[f972])).

fof(f972,plain,
    ( $false
    | spl3_15
    | ~ spl3_91 ),
    inference(resolution,[],[f930,f54])).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f930,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_15
    | ~ spl3_91 ),
    inference(backward_demodulation,[],[f202,f911])).

fof(f911,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_91 ),
    inference(avatar_component_clause,[],[f909])).

fof(f909,plain,
    ( spl3_91
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).

fof(f202,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl3_15
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f912,plain,
    ( ~ spl3_26
    | spl3_83
    | spl3_91
    | ~ spl3_34
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f907,f308,f175,f116,f304,f256,f327,f909,f802,f274])).

fof(f274,plain,
    ( spl3_26
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f802,plain,
    ( spl3_83
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f327,plain,
    ( spl3_34
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f256,plain,
    ( spl3_22
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f304,plain,
    ( spl3_30
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f116,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f175,plain,
    ( spl3_13
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f308,plain,
    ( spl3_31
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f907,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f906])).

fof(f906,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f899,f406])).

fof(f406,plain,
    ( k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f186,f309])).

fof(f309,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f186,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f51,f177])).

fof(f177,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f51,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f899,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(resolution,[],[f474,f189])).

fof(f189,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f118,f177])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f474,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X2
      | k2_relset_1(X1,X2,X0) != X2
      | k1_relat_1(X0) = X1
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(forward_demodulation,[],[f472,f77])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f57,f55])).

fof(f55,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f472,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) = k2_relat_1(k6_partfun1(X1))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X2
      | k2_relset_1(X1,X2,X0) != X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f467])).

fof(f467,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) = k2_relat_1(k6_partfun1(X1))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(X0)
      | k2_relset_1(X1,X2,X0) != X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(superposition,[],[f67,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f67,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f805,plain,
    ( ~ spl3_34
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_83
    | spl3_82 ),
    inference(avatar_split_clause,[],[f800,f796,f802,f304,f256,f327])).

fof(f796,plain,
    ( spl3_82
  <=> u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f800,plain,
    ( u1_struct_0(sK0) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_82 ),
    inference(superposition,[],[f798,f65])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f798,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | spl3_82 ),
    inference(avatar_component_clause,[],[f796])).

fof(f799,plain,
    ( ~ spl3_60
    | ~ spl3_82
    | spl3_61 ),
    inference(avatar_split_clause,[],[f789,f591,f796,f587])).

fof(f587,plain,
    ( spl3_60
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f591,plain,
    ( spl3_61
  <=> u1_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f789,plain,
    ( u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | spl3_61 ),
    inference(superposition,[],[f593,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f593,plain,
    ( u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f591])).

fof(f762,plain,
    ( ~ spl3_34
    | ~ spl3_22
    | ~ spl3_30
    | ~ spl3_27
    | spl3_62 ),
    inference(avatar_split_clause,[],[f756,f595,f278,f304,f256,f327])).

fof(f278,plain,
    ( spl3_27
  <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f595,plain,
    ( spl3_62
  <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f756,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_62 ),
    inference(superposition,[],[f597,f63])).

fof(f63,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f597,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | spl3_62 ),
    inference(avatar_component_clause,[],[f595])).

fof(f603,plain,
    ( ~ spl3_22
    | ~ spl3_26
    | ~ spl3_47
    | ~ spl3_30
    | ~ spl3_13
    | ~ spl3_31
    | spl3_60 ),
    inference(avatar_split_clause,[],[f602,f587,f308,f175,f304,f427,f274,f256])).

fof(f427,plain,
    ( spl3_47
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f602,plain,
    ( ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_13
    | ~ spl3_31
    | spl3_60 ),
    inference(trivial_inequality_removal,[],[f601])).

fof(f601,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_13
    | ~ spl3_31
    | spl3_60 ),
    inference(forward_demodulation,[],[f599,f406])).

fof(f599,plain,
    ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl3_60 ),
    inference(resolution,[],[f589,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f589,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | spl3_60 ),
    inference(avatar_component_clause,[],[f587])).

fof(f598,plain,
    ( ~ spl3_29
    | ~ spl3_37
    | ~ spl3_60
    | ~ spl3_61
    | ~ spl3_57
    | ~ spl3_62
    | spl3_48 ),
    inference(avatar_split_clause,[],[f580,f431,f595,f509,f591,f587,f347,f300])).

fof(f300,plain,
    ( spl3_29
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f347,plain,
    ( spl3_37
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f509,plain,
    ( spl3_57
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f431,plain,
    ( spl3_48
  <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f580,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_48 ),
    inference(superposition,[],[f433,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f433,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f431])).

fof(f518,plain,
    ( ~ spl3_7
    | ~ spl3_13
    | spl3_47 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | ~ spl3_7
    | ~ spl3_13
    | spl3_47 ),
    inference(resolution,[],[f429,f189])).

fof(f429,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f427])).

fof(f514,plain,
    ( ~ spl3_34
    | ~ spl3_22
    | ~ spl3_30
    | spl3_57 ),
    inference(avatar_split_clause,[],[f513,f509,f304,f256,f327])).

fof(f513,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_57 ),
    inference(resolution,[],[f511,f62])).

fof(f62,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f511,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f509])).

fof(f434,plain,
    ( ~ spl3_22
    | ~ spl3_26
    | ~ spl3_47
    | ~ spl3_30
    | ~ spl3_48
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f425,f308,f175,f431,f304,f427,f274,f256])).

fof(f425,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f424])).

fof(f424,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2)
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_13
    | ~ spl3_31 ),
    inference(forward_demodulation,[],[f417,f406])).

fof(f417,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f403,f73])).

fof(f403,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_31 ),
    inference(backward_demodulation,[],[f53,f309])).

fof(f53,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f411,plain,
    ( ~ spl3_8
    | ~ spl3_13
    | spl3_26 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl3_8
    | ~ spl3_13
    | spl3_26 ),
    inference(resolution,[],[f276,f190])).

fof(f190,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_8
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f123,f177])).

fof(f123,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_8
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f276,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f274])).

fof(f367,plain,
    ( ~ spl3_13
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | ~ spl3_13
    | spl3_31 ),
    inference(resolution,[],[f365,f47])).

fof(f47,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f365,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl3_13
    | spl3_31 ),
    inference(trivial_inequality_removal,[],[f364])).

fof(f364,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_13
    | spl3_31 ),
    inference(forward_demodulation,[],[f363,f177])).

fof(f363,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | ~ l1_struct_0(sK1)
    | spl3_31 ),
    inference(superposition,[],[f310,f58])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f310,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f308])).

fof(f357,plain,(
    spl3_34 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl3_34 ),
    inference(resolution,[],[f329,f135])).

fof(f135,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f329,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f327])).

fof(f350,plain,
    ( ~ spl3_22
    | ~ spl3_26
    | spl3_37
    | ~ spl3_30
    | ~ spl3_17
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f333,f175,f116,f213,f304,f347,f274,f256])).

fof(f213,plain,
    ( spl3_17
  <=> k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f333,plain,
    ( k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(resolution,[],[f71,f189])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f330,plain,
    ( ~ spl3_34
    | ~ spl3_22
    | ~ spl3_30
    | spl3_29 ),
    inference(avatar_split_clause,[],[f325,f300,f304,f256,f327])).

fof(f325,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_29 ),
    inference(resolution,[],[f301,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f301,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f300])).

fof(f324,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl3_30 ),
    inference(resolution,[],[f306,f52])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f306,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f304])).

fof(f288,plain,(
    spl3_22 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl3_22 ),
    inference(resolution,[],[f258,f48])).

fof(f48,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f258,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_22 ),
    inference(avatar_component_clause,[],[f256])).

fof(f281,plain,
    ( ~ spl3_22
    | ~ spl3_26
    | spl3_27
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f253,f175,f116,f278,f274,f256])).

fof(f253,plain,
    ( r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_7
    | ~ spl3_13 ),
    inference(resolution,[],[f80,f189])).

% (22366)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f79])).

% (22384)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(condensation,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f240,plain,(
    spl3_12 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl3_12 ),
    inference(resolution,[],[f173,f50])).

fof(f173,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f216,plain,
    ( ~ spl3_5
    | spl3_17
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f211,f175,f213,f107])).

fof(f107,plain,
    ( spl3_5
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f211,plain,
    ( k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f205,f177])).

fof(f205,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f186,f58])).

fof(f203,plain,
    ( spl3_14
    | ~ spl3_5
    | ~ spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f194,f175,f200,f107,f196])).

fof(f194,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_13 ),
    inference(superposition,[],[f59,f177])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f182,plain,
    ( ~ spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f166,f175,f171])).

fof(f166,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(superposition,[],[f51,f69])).

fof(f128,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f109,f47])).

fof(f109,plain,
    ( ~ l1_struct_0(sK1)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f124,plain,
    ( ~ spl3_5
    | spl3_8 ),
    inference(avatar_split_clause,[],[f86,f121,f107])).

fof(f86,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f49,f58])).

fof(f49,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,
    ( ~ spl3_5
    | spl3_7 ),
    inference(avatar_split_clause,[],[f85,f116,f107])).

fof(f85,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f50,f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:01:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (22379)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (22370)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (22370)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (22381)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (22369)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (22368)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f985,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f119,f124,f128,f182,f203,f216,f240,f281,f288,f324,f330,f350,f357,f367,f411,f434,f514,f518,f598,f603,f762,f799,f805,f912,f973,f984])).
% 0.20/0.47  fof(f984,plain,(
% 0.20/0.47    ~spl3_14),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f983])).
% 0.20/0.47  fof(f983,plain,(
% 0.20/0.47    $false | ~spl3_14),
% 0.20/0.47    inference(resolution,[],[f198,f46])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ~v2_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f43,f42,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f16])).
% 0.20/0.47  fof(f16,conjecture,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    v2_struct_0(sK1) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f196])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    spl3_14 <=> v2_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f973,plain,(
% 0.20/0.47    spl3_15 | ~spl3_91),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f972])).
% 0.20/0.47  fof(f972,plain,(
% 0.20/0.47    $false | (spl3_15 | ~spl3_91)),
% 0.20/0.47    inference(resolution,[],[f930,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f930,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | (spl3_15 | ~spl3_91)),
% 0.20/0.47    inference(backward_demodulation,[],[f202,f911])).
% 0.20/0.47  fof(f911,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_91),
% 0.20/0.47    inference(avatar_component_clause,[],[f909])).
% 0.20/0.47  fof(f909,plain,(
% 0.20/0.47    spl3_91 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_91])])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_15),
% 0.20/0.47    inference(avatar_component_clause,[],[f200])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    spl3_15 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.47  fof(f912,plain,(
% 0.20/0.47    ~spl3_26 | spl3_83 | spl3_91 | ~spl3_34 | ~spl3_22 | ~spl3_30 | ~spl3_7 | ~spl3_13 | ~spl3_31),
% 0.20/0.47    inference(avatar_split_clause,[],[f907,f308,f175,f116,f304,f256,f327,f909,f802,f274])).
% 0.20/0.47  fof(f274,plain,(
% 0.20/0.47    spl3_26 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.47  fof(f802,plain,(
% 0.20/0.47    spl3_83 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.20/0.47  fof(f327,plain,(
% 0.20/0.47    spl3_34 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.20/0.47  fof(f256,plain,(
% 0.20/0.47    spl3_22 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.47  fof(f304,plain,(
% 0.20/0.47    spl3_30 <=> v2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl3_13 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f308,plain,(
% 0.20/0.47    spl3_31 <=> u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.47  fof(f907,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_7 | ~spl3_13 | ~spl3_31)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f906])).
% 0.20/0.47  fof(f906,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_7 | ~spl3_13 | ~spl3_31)),
% 0.20/0.47    inference(forward_demodulation,[],[f899,f406])).
% 0.20/0.47  fof(f406,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_13 | ~spl3_31)),
% 0.20/0.47    inference(backward_demodulation,[],[f186,f309])).
% 0.20/0.47  fof(f309,plain,(
% 0.20/0.47    u1_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f308])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_13),
% 0.20/0.47    inference(backward_demodulation,[],[f51,f177])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f175])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f899,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | u1_struct_0(sK0) = k1_relat_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_7 | ~spl3_13)),
% 0.20/0.47    inference(resolution,[],[f474,f189])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f118,f177])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f474,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X2 | k2_relset_1(X1,X2,X0) != X2 | k1_relat_1(X0) = X1 | ~v1_funct_2(X0,X1,X2)) )),
% 0.20/0.47    inference(forward_demodulation,[],[f472,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f57,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.47  fof(f472,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relat_1(X0) = k2_relat_1(k6_partfun1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X2 | k2_relset_1(X1,X2,X0) != X2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f467])).
% 0.20/0.47  fof(f467,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_relat_1(X0) = k2_relat_1(k6_partfun1(X1)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X2 | ~v2_funct_1(X0) | k2_relset_1(X1,X2,X0) != X2 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.20/0.47    inference(superposition,[],[f67,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 0.20/0.47  fof(f805,plain,(
% 0.20/0.47    ~spl3_34 | ~spl3_22 | ~spl3_30 | ~spl3_83 | spl3_82),
% 0.20/0.47    inference(avatar_split_clause,[],[f800,f796,f802,f304,f256,f327])).
% 0.20/0.47  fof(f796,plain,(
% 0.20/0.47    spl3_82 <=> u1_struct_0(sK0) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.20/0.47  fof(f800,plain,(
% 0.20/0.47    u1_struct_0(sK0) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_82),
% 0.20/0.47    inference(superposition,[],[f798,f65])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.47  fof(f798,plain,(
% 0.20/0.47    u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | spl3_82),
% 0.20/0.47    inference(avatar_component_clause,[],[f796])).
% 0.20/0.47  fof(f799,plain,(
% 0.20/0.47    ~spl3_60 | ~spl3_82 | spl3_61),
% 0.20/0.47    inference(avatar_split_clause,[],[f789,f591,f796,f587])).
% 0.20/0.47  fof(f587,plain,(
% 0.20/0.47    spl3_60 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.20/0.47  fof(f591,plain,(
% 0.20/0.47    spl3_61 <=> u1_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.20/0.47  fof(f789,plain,(
% 0.20/0.47    u1_struct_0(sK0) != k2_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) | spl3_61),
% 0.20/0.47    inference(superposition,[],[f593,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f593,plain,(
% 0.20/0.47    u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)) | spl3_61),
% 0.20/0.47    inference(avatar_component_clause,[],[f591])).
% 0.20/0.47  fof(f762,plain,(
% 0.20/0.47    ~spl3_34 | ~spl3_22 | ~spl3_30 | ~spl3_27 | spl3_62),
% 0.20/0.47    inference(avatar_split_clause,[],[f756,f595,f278,f304,f256,f327])).
% 0.20/0.47  fof(f278,plain,(
% 0.20/0.47    spl3_27 <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f595,plain,(
% 0.20/0.47    spl3_62 <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.20/0.47  fof(f756,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_62),
% 0.20/0.47    inference(superposition,[],[f597,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.20/0.47  fof(f597,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | spl3_62),
% 0.20/0.47    inference(avatar_component_clause,[],[f595])).
% 0.20/0.47  fof(f603,plain,(
% 0.20/0.47    ~spl3_22 | ~spl3_26 | ~spl3_47 | ~spl3_30 | ~spl3_13 | ~spl3_31 | spl3_60),
% 0.20/0.47    inference(avatar_split_clause,[],[f602,f587,f308,f175,f304,f427,f274,f256])).
% 0.20/0.47  fof(f427,plain,(
% 0.20/0.47    spl3_47 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.47  fof(f602,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_13 | ~spl3_31 | spl3_60)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f601])).
% 0.20/0.47  fof(f601,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_13 | ~spl3_31 | spl3_60)),
% 0.20/0.47    inference(forward_demodulation,[],[f599,f406])).
% 0.20/0.47  fof(f599,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | spl3_60),
% 0.20/0.47    inference(resolution,[],[f589,f72])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.47  fof(f589,plain,(
% 0.20/0.47    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) | spl3_60),
% 0.20/0.47    inference(avatar_component_clause,[],[f587])).
% 0.20/0.47  fof(f598,plain,(
% 0.20/0.47    ~spl3_29 | ~spl3_37 | ~spl3_60 | ~spl3_61 | ~spl3_57 | ~spl3_62 | spl3_48),
% 0.20/0.47    inference(avatar_split_clause,[],[f580,f431,f595,f509,f591,f587,f347,f300])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    spl3_29 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.47  fof(f347,plain,(
% 0.20/0.47    spl3_37 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.47  fof(f509,plain,(
% 0.20/0.47    spl3_57 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.47  fof(f431,plain,(
% 0.20/0.47    spl3_48 <=> r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.47  fof(f580,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | ~v2_funct_1(k2_funct_1(sK2)) | u1_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),u1_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | spl3_48),
% 0.20/0.47    inference(superposition,[],[f433,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.47  fof(f433,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2) | spl3_48),
% 0.20/0.47    inference(avatar_component_clause,[],[f431])).
% 0.20/0.47  fof(f518,plain,(
% 0.20/0.47    ~spl3_7 | ~spl3_13 | spl3_47),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f516])).
% 0.20/0.47  fof(f516,plain,(
% 0.20/0.47    $false | (~spl3_7 | ~spl3_13 | spl3_47)),
% 0.20/0.47    inference(resolution,[],[f429,f189])).
% 0.20/0.47  fof(f429,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | spl3_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f427])).
% 0.20/0.47  fof(f514,plain,(
% 0.20/0.47    ~spl3_34 | ~spl3_22 | ~spl3_30 | spl3_57),
% 0.20/0.47    inference(avatar_split_clause,[],[f513,f509,f304,f256,f327])).
% 0.20/0.47  fof(f513,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_57),
% 0.20/0.47    inference(resolution,[],[f511,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.20/0.47  fof(f511,plain,(
% 0.20/0.47    ~v2_funct_1(k2_funct_1(sK2)) | spl3_57),
% 0.20/0.47    inference(avatar_component_clause,[],[f509])).
% 0.20/0.47  fof(f434,plain,(
% 0.20/0.47    ~spl3_22 | ~spl3_26 | ~spl3_47 | ~spl3_30 | ~spl3_48 | ~spl3_13 | ~spl3_31),
% 0.20/0.47    inference(avatar_split_clause,[],[f425,f308,f175,f431,f304,f427,f274,f256])).
% 0.20/0.47  fof(f425,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_13 | ~spl3_31)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f424])).
% 0.20/0.47  fof(f424,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_13 | ~spl3_31)),
% 0.20/0.47    inference(forward_demodulation,[],[f417,f406])).
% 0.20/0.47  fof(f417,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_funct_1(sK2)),sK2) | ~v2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_31),
% 0.20/0.47    inference(superposition,[],[f403,f73])).
% 0.20/0.47  fof(f403,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~spl3_31),
% 0.20/0.47    inference(backward_demodulation,[],[f53,f309])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f411,plain,(
% 0.20/0.47    ~spl3_8 | ~spl3_13 | spl3_26),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f409])).
% 0.20/0.47  fof(f409,plain,(
% 0.20/0.47    $false | (~spl3_8 | ~spl3_13 | spl3_26)),
% 0.20/0.47    inference(resolution,[],[f276,f190])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_8 | ~spl3_13)),
% 0.20/0.47    inference(backward_demodulation,[],[f123,f177])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f121])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    spl3_8 <=> v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | spl3_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f274])).
% 0.20/0.47  fof(f367,plain,(
% 0.20/0.47    ~spl3_13 | spl3_31),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f366])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    $false | (~spl3_13 | spl3_31)),
% 0.20/0.47    inference(resolution,[],[f365,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    l1_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f365,plain,(
% 0.20/0.47    ~l1_struct_0(sK1) | (~spl3_13 | spl3_31)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f364])).
% 0.20/0.47  fof(f364,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~l1_struct_0(sK1) | (~spl3_13 | spl3_31)),
% 0.20/0.47    inference(forward_demodulation,[],[f363,f177])).
% 0.20/0.47  fof(f363,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k2_relat_1(sK2) | ~l1_struct_0(sK1) | spl3_31),
% 0.20/0.47    inference(superposition,[],[f310,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.47  fof(f310,plain,(
% 0.20/0.47    u1_struct_0(sK1) != k2_relat_1(sK2) | spl3_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f308])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    spl3_34),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f356])).
% 0.20/0.47  fof(f356,plain,(
% 0.20/0.47    $false | spl3_34),
% 0.20/0.47    inference(resolution,[],[f329,f135])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f68,f50])).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f329,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | spl3_34),
% 0.20/0.47    inference(avatar_component_clause,[],[f327])).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    ~spl3_22 | ~spl3_26 | spl3_37 | ~spl3_30 | ~spl3_17 | ~spl3_7 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f333,f175,f116,f213,f304,f347,f274,f256])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    spl3_17 <=> k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f333,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_7 | ~spl3_13)),
% 0.20/0.47    inference(resolution,[],[f71,f189])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f34])).
% 0.20/0.47  fof(f330,plain,(
% 0.20/0.47    ~spl3_34 | ~spl3_22 | ~spl3_30 | spl3_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f325,f300,f304,f256,f327])).
% 0.20/0.47  fof(f325,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_29),
% 0.20/0.47    inference(resolution,[],[f301,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f301,plain,(
% 0.20/0.47    ~v1_funct_1(k2_funct_1(sK2)) | spl3_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f300])).
% 0.20/0.47  fof(f324,plain,(
% 0.20/0.47    spl3_30),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f323])).
% 0.20/0.47  fof(f323,plain,(
% 0.20/0.47    $false | spl3_30),
% 0.20/0.47    inference(resolution,[],[f306,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    v2_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f304])).
% 0.20/0.47  fof(f288,plain,(
% 0.20/0.47    spl3_22),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f287])).
% 0.20/0.47  fof(f287,plain,(
% 0.20/0.47    $false | spl3_22),
% 0.20/0.47    inference(resolution,[],[f258,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | spl3_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f256])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    ~spl3_22 | ~spl3_26 | spl3_27 | ~spl3_7 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f253,f175,f116,f278,f274,f256])).
% 0.20/0.47  fof(f253,plain,(
% 0.20/0.47    r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_7 | ~spl3_13)),
% 0.20/0.47    inference(resolution,[],[f80,f189])).
% 0.20/0.47  % (22366)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.20/0.47    inference(duplicate_literal_removal,[],[f79])).
% 0.20/0.47  % (22384)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.20/0.47    inference(condensation,[],[f76])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f40])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f237])).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    $false | spl3_12),
% 0.20/0.47    inference(resolution,[],[f173,f50])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    ~spl3_5 | spl3_17 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f211,f175,f213,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    spl3_5 <=> l1_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f211,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~l1_struct_0(sK1) | ~spl3_13),
% 0.20/0.47    inference(forward_demodulation,[],[f205,f177])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~l1_struct_0(sK1) | ~spl3_13),
% 0.20/0.47    inference(superposition,[],[f186,f58])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    spl3_14 | ~spl3_5 | ~spl3_15 | ~spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f194,f175,f200,f107,f196])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_13),
% 0.20/0.47    inference(superposition,[],[f59,f177])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~spl3_12 | spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f166,f175,f171])).
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    inference(superposition,[],[f51,f69])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    $false | spl3_5),
% 0.20/0.47    inference(resolution,[],[f109,f47])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ~l1_struct_0(sK1) | spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f107])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    ~spl3_5 | spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f86,f121,f107])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.20/0.47    inference(superposition,[],[f49,f58])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f44])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    ~spl3_5 | spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f85,f116,f107])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~l1_struct_0(sK1)),
% 0.20/0.47    inference(superposition,[],[f50,f58])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22370)------------------------------
% 0.20/0.47  % (22370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22370)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22370)Memory used [KB]: 6652
% 0.20/0.47  % (22370)Time elapsed: 0.059 s
% 0.20/0.47  % (22370)------------------------------
% 0.20/0.47  % (22370)------------------------------
% 0.20/0.47  % (22374)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (22360)Success in time 0.118 s
%------------------------------------------------------------------------------
