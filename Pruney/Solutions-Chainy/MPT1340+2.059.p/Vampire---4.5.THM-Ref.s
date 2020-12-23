%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:26 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  188 (1191 expanded)
%              Number of leaves         :   25 ( 422 expanded)
%              Depth                    :   26
%              Number of atoms          :  649 (8846 expanded)
%              Number of equality atoms :  124 (1182 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f124,f129,f175,f361,f413])).

fof(f413,plain,(
    ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f412])).

fof(f412,plain,
    ( $false
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f405,f174])).

fof(f174,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl3_6
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f405,plain,(
    ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f404,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f404,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f219,f57])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f219,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(superposition,[],[f68,f95])).

fof(f95,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f66,f57])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f361,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f359,f237])).

fof(f237,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2,sK2)
    | ~ spl3_5 ),
    inference(superposition,[],[f180,f214])).

fof(f214,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f213,f130])).

fof(f130,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f126,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f126,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f67,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f213,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f212,f133])).

fof(f133,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f132,f94])).

fof(f94,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f66,f55])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f132,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f60])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f212,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f170,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f170,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_5
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f180,plain,(
    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(forward_demodulation,[],[f179,f94])).

fof(f179,plain,(
    r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK2) ),
    inference(forward_demodulation,[],[f178,f95])).

fof(f178,plain,(
    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f177,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f176,f59])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f176,plain,
    ( r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f93,f60])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f359,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2,sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f358,f294])).

fof(f294,plain,
    ( sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f293,f137])).

fof(f137,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f136,f130])).

fof(f136,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f58])).

fof(f134,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f71,f62])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f293,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f292,f214])).

fof(f292,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f291,f267])).

fof(f267,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f266,f147])).

fof(f147,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f146,f130])).

fof(f146,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f144,f58])).

fof(f144,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f73,f62])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f266,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f254,f214])).

fof(f254,plain,(
    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f197,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f197,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f196,f95])).

fof(f196,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f195,f94])).

fof(f195,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f194,f95])).

fof(f194,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f193,f61])).

fof(f61,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f193,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f192,f58])).

fof(f192,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f191,f59])).

fof(f191,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f190,f62])).

fof(f190,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f87,f60])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f291,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f290,f214])).

fof(f290,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f289,f131])).

fof(f131,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f125,f130])).

fof(f125,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f58])).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f289,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f288,f189])).

fof(f189,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f188,f95])).

fof(f188,plain,(
    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f187,f94])).

fof(f187,plain,(
    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f186,f95])).

fof(f186,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f185,f61])).

fof(f185,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f184,f58])).

fof(f184,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f183,f59])).

fof(f183,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f182,f62])).

fof(f182,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f86,f60])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f288,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f259,f249])).

fof(f249,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f248,f123])).

fof(f123,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_4
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f248,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f247,f131])).

fof(f247,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f246,f130])).

fof(f246,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f245,f58])).

fof(f245,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f244,f142])).

fof(f142,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f141,f130])).

fof(f141,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f139,f58])).

fof(f139,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f72,f62])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f244,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f242,f65])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f242,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f77,f155])).

fof(f155,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f154,f130])).

fof(f154,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f152,f58])).

fof(f152,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f74,f62])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f259,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f197,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f358,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f353,f214])).

fof(f353,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2) ),
    inference(superposition,[],[f100,f211])).

fof(f211,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f210,f94])).

fof(f210,plain,(
    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f209,f95])).

fof(f209,plain,(
    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f208,f95])).

fof(f208,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f207,f61])).

fof(f207,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f206,f58])).

fof(f206,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f59])).

fof(f205,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f204,f62])).

fof(f204,plain,
    ( ~ v2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f88,f60])).

fof(f100,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f96,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(superposition,[],[f63,f94])).

fof(f63,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f175,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f166,f172,f168])).

fof(f166,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f165,f95])).

fof(f165,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f164,f94])).

fof(f164,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f163,f58])).

fof(f163,plain,
    ( ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f162,f59])).

fof(f162,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | v1_partfun1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f80,f60])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f129,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl3_3 ),
    inference(subsumption_resolution,[],[f127,f78])).

fof(f127,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl3_3 ),
    inference(subsumption_resolution,[],[f126,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f115,f121,f117])).

fof(f115,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f69,f58])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (826769409)
% 0.13/0.36  ipcrm: permission denied for id (830767106)
% 0.13/0.37  ipcrm: permission denied for id (826867715)
% 0.13/0.37  ipcrm: permission denied for id (830799876)
% 0.13/0.37  ipcrm: permission denied for id (826933253)
% 0.13/0.37  ipcrm: permission denied for id (826966022)
% 0.13/0.37  ipcrm: permission denied for id (827064329)
% 0.13/0.37  ipcrm: permission denied for id (830898186)
% 0.13/0.37  ipcrm: permission denied for id (827129867)
% 0.13/0.38  ipcrm: permission denied for id (827162637)
% 0.13/0.38  ipcrm: permission denied for id (827228174)
% 0.13/0.38  ipcrm: permission denied for id (827260943)
% 0.13/0.38  ipcrm: permission denied for id (827293712)
% 0.13/0.38  ipcrm: permission denied for id (827326481)
% 0.13/0.38  ipcrm: permission denied for id (827359250)
% 0.13/0.38  ipcrm: permission denied for id (827392019)
% 0.13/0.39  ipcrm: permission denied for id (830963732)
% 0.13/0.39  ipcrm: permission denied for id (827424789)
% 0.13/0.39  ipcrm: permission denied for id (830996502)
% 0.13/0.39  ipcrm: permission denied for id (827490327)
% 0.13/0.39  ipcrm: permission denied for id (827555865)
% 0.13/0.39  ipcrm: permission denied for id (831062042)
% 0.13/0.39  ipcrm: permission denied for id (831127579)
% 0.13/0.40  ipcrm: permission denied for id (827654172)
% 0.13/0.40  ipcrm: permission denied for id (827686941)
% 0.13/0.40  ipcrm: permission denied for id (827719710)
% 0.13/0.40  ipcrm: permission denied for id (831160351)
% 0.13/0.40  ipcrm: permission denied for id (831225889)
% 0.13/0.40  ipcrm: permission denied for id (831291427)
% 0.13/0.40  ipcrm: permission denied for id (827883556)
% 0.13/0.41  ipcrm: permission denied for id (831389735)
% 0.13/0.41  ipcrm: permission denied for id (827981864)
% 0.21/0.41  ipcrm: permission denied for id (828047402)
% 0.21/0.41  ipcrm: permission denied for id (831488044)
% 0.21/0.42  ipcrm: permission denied for id (831520813)
% 0.21/0.42  ipcrm: permission denied for id (828178478)
% 0.21/0.42  ipcrm: permission denied for id (831553583)
% 0.21/0.42  ipcrm: permission denied for id (828244016)
% 0.21/0.42  ipcrm: permission denied for id (828309555)
% 0.21/0.42  ipcrm: permission denied for id (828342324)
% 0.21/0.42  ipcrm: permission denied for id (828375093)
% 0.21/0.43  ipcrm: permission denied for id (831651894)
% 0.21/0.43  ipcrm: permission denied for id (828506168)
% 0.21/0.43  ipcrm: permission denied for id (828604474)
% 0.21/0.43  ipcrm: permission denied for id (828670011)
% 0.21/0.43  ipcrm: permission denied for id (828702780)
% 0.21/0.43  ipcrm: permission denied for id (828735549)
% 0.21/0.43  ipcrm: permission denied for id (828768318)
% 0.21/0.44  ipcrm: permission denied for id (831750207)
% 0.21/0.44  ipcrm: permission denied for id (831782976)
% 0.21/0.44  ipcrm: permission denied for id (828932164)
% 0.21/0.44  ipcrm: permission denied for id (831979590)
% 0.21/0.45  ipcrm: permission denied for id (832012359)
% 0.21/0.45  ipcrm: permission denied for id (829063240)
% 0.21/0.45  ipcrm: permission denied for id (832045129)
% 0.21/0.45  ipcrm: permission denied for id (829096010)
% 0.21/0.45  ipcrm: permission denied for id (829161548)
% 0.21/0.45  ipcrm: permission denied for id (832110669)
% 0.21/0.45  ipcrm: permission denied for id (829227086)
% 0.21/0.46  ipcrm: permission denied for id (832208977)
% 0.21/0.46  ipcrm: permission denied for id (832241746)
% 0.21/0.46  ipcrm: permission denied for id (829423700)
% 0.21/0.46  ipcrm: permission denied for id (829456469)
% 0.21/0.46  ipcrm: permission denied for id (832307286)
% 0.21/0.46  ipcrm: permission denied for id (829522008)
% 0.21/0.47  ipcrm: permission denied for id (832372825)
% 0.21/0.47  ipcrm: permission denied for id (829554778)
% 0.21/0.47  ipcrm: permission denied for id (829587547)
% 0.21/0.47  ipcrm: permission denied for id (832471134)
% 0.21/0.48  ipcrm: permission denied for id (829751393)
% 0.21/0.48  ipcrm: permission denied for id (832634979)
% 0.21/0.48  ipcrm: permission denied for id (829849700)
% 0.21/0.48  ipcrm: permission denied for id (832667749)
% 0.21/0.48  ipcrm: permission denied for id (832700518)
% 0.21/0.48  ipcrm: permission denied for id (829980776)
% 0.21/0.49  ipcrm: permission denied for id (832831594)
% 0.21/0.49  ipcrm: permission denied for id (832864363)
% 0.21/0.49  ipcrm: permission denied for id (832897132)
% 0.21/0.49  ipcrm: permission denied for id (830111853)
% 0.21/0.49  ipcrm: permission denied for id (830144622)
% 0.21/0.49  ipcrm: permission denied for id (830177391)
% 0.21/0.49  ipcrm: permission denied for id (830210160)
% 0.21/0.49  ipcrm: permission denied for id (832929905)
% 0.21/0.50  ipcrm: permission denied for id (832995443)
% 0.21/0.50  ipcrm: permission denied for id (833093749)
% 0.21/0.50  ipcrm: permission denied for id (830406774)
% 0.21/0.50  ipcrm: permission denied for id (830439543)
% 0.21/0.50  ipcrm: permission denied for id (830505081)
% 0.21/0.51  ipcrm: permission denied for id (833192059)
% 0.21/0.51  ipcrm: permission denied for id (830636157)
% 0.21/0.51  ipcrm: permission denied for id (830668926)
% 0.97/0.62  % (31510)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.97/0.62  % (31510)Refutation found. Thanks to Tanya!
% 0.97/0.62  % SZS status Theorem for theBenchmark
% 0.97/0.62  % (31504)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.97/0.63  % (31519)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.97/0.63  % (31512)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.97/0.63  % SZS output start Proof for theBenchmark
% 0.97/0.63  fof(f419,plain,(
% 0.97/0.63    $false),
% 0.97/0.63    inference(avatar_sat_refutation,[],[f124,f129,f175,f361,f413])).
% 0.97/0.63  fof(f413,plain,(
% 0.97/0.63    ~spl3_6),
% 0.97/0.63    inference(avatar_contradiction_clause,[],[f412])).
% 0.97/0.63  fof(f412,plain,(
% 0.97/0.63    $false | ~spl3_6),
% 0.97/0.63    inference(subsumption_resolution,[],[f405,f174])).
% 0.97/0.63  fof(f174,plain,(
% 0.97/0.63    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_6),
% 0.97/0.63    inference(avatar_component_clause,[],[f172])).
% 0.97/0.63  fof(f172,plain,(
% 0.97/0.63    spl3_6 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.97/0.63  fof(f405,plain,(
% 0.97/0.63    ~v1_xboole_0(k2_struct_0(sK1))),
% 0.97/0.63    inference(subsumption_resolution,[],[f404,f56])).
% 0.97/0.63  fof(f56,plain,(
% 0.97/0.63    ~v2_struct_0(sK1)),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f52,plain,(
% 0.97/0.63    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.97/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).
% 0.97/0.63  fof(f49,plain,(
% 0.97/0.63    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.97/0.63    introduced(choice_axiom,[])).
% 0.97/0.63  fof(f50,plain,(
% 0.97/0.63    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.97/0.63    introduced(choice_axiom,[])).
% 0.97/0.63  fof(f51,plain,(
% 0.97/0.63    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.97/0.63    introduced(choice_axiom,[])).
% 0.97/0.63  fof(f22,plain,(
% 0.97/0.63    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.97/0.63    inference(flattening,[],[f21])).
% 0.97/0.63  fof(f21,plain,(
% 0.97/0.63    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.97/0.63    inference(ennf_transformation,[],[f19])).
% 0.97/0.63  fof(f19,negated_conjecture,(
% 0.97/0.63    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.97/0.63    inference(negated_conjecture,[],[f18])).
% 0.97/0.63  fof(f18,conjecture,(
% 0.97/0.63    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.97/0.63  fof(f404,plain,(
% 0.97/0.63    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1)),
% 0.97/0.63    inference(subsumption_resolution,[],[f219,f57])).
% 0.97/0.63  fof(f57,plain,(
% 0.97/0.63    l1_struct_0(sK1)),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f219,plain,(
% 0.97/0.63    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.97/0.63    inference(superposition,[],[f68,f95])).
% 0.97/0.63  fof(f95,plain,(
% 0.97/0.63    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.97/0.63    inference(resolution,[],[f66,f57])).
% 0.97/0.63  fof(f66,plain,(
% 0.97/0.63    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f23])).
% 0.97/0.63  fof(f23,plain,(
% 0.97/0.63    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.97/0.63    inference(ennf_transformation,[],[f15])).
% 0.97/0.63  fof(f15,axiom,(
% 0.97/0.63    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.97/0.63  fof(f68,plain,(
% 0.97/0.63    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f26])).
% 0.97/0.63  fof(f26,plain,(
% 0.97/0.63    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.97/0.63    inference(flattening,[],[f25])).
% 0.97/0.63  fof(f25,plain,(
% 0.97/0.63    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.97/0.63    inference(ennf_transformation,[],[f16])).
% 0.97/0.63  fof(f16,axiom,(
% 0.97/0.63    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.97/0.63  fof(f361,plain,(
% 0.97/0.63    ~spl3_4 | ~spl3_5),
% 0.97/0.63    inference(avatar_contradiction_clause,[],[f360])).
% 0.97/0.63  fof(f360,plain,(
% 0.97/0.63    $false | (~spl3_4 | ~spl3_5)),
% 0.97/0.63    inference(subsumption_resolution,[],[f359,f237])).
% 0.97/0.63  fof(f237,plain,(
% 0.97/0.63    r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2,sK2) | ~spl3_5),
% 0.97/0.63    inference(superposition,[],[f180,f214])).
% 0.97/0.63  fof(f214,plain,(
% 0.97/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_5),
% 0.97/0.63    inference(subsumption_resolution,[],[f213,f130])).
% 0.97/0.63  fof(f130,plain,(
% 0.97/0.63    v1_relat_1(sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f126,f78])).
% 0.97/0.63  fof(f78,plain,(
% 0.97/0.63    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.97/0.63    inference(cnf_transformation,[],[f2])).
% 0.97/0.63  fof(f2,axiom,(
% 0.97/0.63    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.97/0.63  fof(f126,plain,(
% 0.97/0.63    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 0.97/0.63    inference(resolution,[],[f67,f60])).
% 0.97/0.63  fof(f60,plain,(
% 0.97/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f67,plain,(
% 0.97/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f24])).
% 0.97/0.63  fof(f24,plain,(
% 0.97/0.63    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.97/0.63    inference(ennf_transformation,[],[f1])).
% 0.97/0.63  fof(f1,axiom,(
% 0.97/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.97/0.63  fof(f213,plain,(
% 0.97/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.97/0.63    inference(subsumption_resolution,[],[f212,f133])).
% 0.97/0.63  fof(f133,plain,(
% 0.97/0.63    v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.97/0.63    inference(forward_demodulation,[],[f132,f94])).
% 0.97/0.63  fof(f94,plain,(
% 0.97/0.63    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.97/0.63    inference(resolution,[],[f66,f55])).
% 0.97/0.63  fof(f55,plain,(
% 0.97/0.63    l1_struct_0(sK0)),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f132,plain,(
% 0.97/0.63    v4_relat_1(sK2,u1_struct_0(sK0))),
% 0.97/0.63    inference(resolution,[],[f84,f60])).
% 0.97/0.63  fof(f84,plain,(
% 0.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f42])).
% 0.97/0.63  fof(f42,plain,(
% 0.97/0.63    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.97/0.63    inference(ennf_transformation,[],[f20])).
% 0.97/0.63  fof(f20,plain,(
% 0.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.97/0.63    inference(pure_predicate_removal,[],[f9])).
% 0.97/0.63  fof(f9,axiom,(
% 0.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.97/0.63  fof(f212,plain,(
% 0.97/0.63    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_5),
% 0.97/0.63    inference(resolution,[],[f170,f81])).
% 0.97/0.63  fof(f81,plain,(
% 0.97/0.63    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f53])).
% 0.97/0.63  fof(f53,plain,(
% 0.97/0.63    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.97/0.63    inference(nnf_transformation,[],[f40])).
% 0.97/0.63  fof(f40,plain,(
% 0.97/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.97/0.63    inference(flattening,[],[f39])).
% 0.97/0.63  fof(f39,plain,(
% 0.97/0.63    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.97/0.63    inference(ennf_transformation,[],[f12])).
% 0.97/0.63  fof(f12,axiom,(
% 0.97/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.97/0.63  fof(f170,plain,(
% 0.97/0.63    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_5),
% 0.97/0.63    inference(avatar_component_clause,[],[f168])).
% 0.97/0.63  fof(f168,plain,(
% 0.97/0.63    spl3_5 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.97/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.97/0.63  fof(f180,plain,(
% 0.97/0.63    r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.97/0.63    inference(forward_demodulation,[],[f179,f94])).
% 0.97/0.63  fof(f179,plain,(
% 0.97/0.63    r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK2)),
% 0.97/0.63    inference(forward_demodulation,[],[f178,f95])).
% 0.97/0.63  fof(f178,plain,(
% 0.97/0.63    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f177,f58])).
% 0.97/0.63  fof(f58,plain,(
% 0.97/0.63    v1_funct_1(sK2)),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f177,plain,(
% 0.97/0.63    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) | ~v1_funct_1(sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f176,f59])).
% 0.97/0.63  fof(f59,plain,(
% 0.97/0.63    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f176,plain,(
% 0.97/0.63    r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.63    inference(resolution,[],[f93,f60])).
% 0.97/0.63  fof(f93,plain,(
% 0.97/0.63    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.97/0.63    inference(duplicate_literal_removal,[],[f92])).
% 0.97/0.63  fof(f92,plain,(
% 0.97/0.63    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.97/0.63    inference(equality_resolution,[],[f90])).
% 0.97/0.63  fof(f90,plain,(
% 0.97/0.63    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f54])).
% 0.97/0.63  fof(f54,plain,(
% 0.97/0.63    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.97/0.63    inference(nnf_transformation,[],[f48])).
% 0.97/0.63  fof(f48,plain,(
% 0.97/0.63    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.97/0.63    inference(flattening,[],[f47])).
% 0.97/0.63  fof(f47,plain,(
% 0.97/0.63    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.97/0.63    inference(ennf_transformation,[],[f13])).
% 0.97/0.63  fof(f13,axiom,(
% 0.97/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.97/0.63  fof(f359,plain,(
% 0.97/0.63    ~r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2,sK2) | (~spl3_4 | ~spl3_5)),
% 0.97/0.63    inference(forward_demodulation,[],[f358,f294])).
% 0.97/0.63  fof(f294,plain,(
% 0.97/0.63    sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.97/0.63    inference(forward_demodulation,[],[f293,f137])).
% 0.97/0.63  fof(f137,plain,(
% 0.97/0.63    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.97/0.63    inference(subsumption_resolution,[],[f136,f130])).
% 0.97/0.63  fof(f136,plain,(
% 0.97/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f134,f58])).
% 0.97/0.63  fof(f134,plain,(
% 0.97/0.63    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.97/0.63    inference(resolution,[],[f71,f62])).
% 0.97/0.63  fof(f62,plain,(
% 0.97/0.63    v2_funct_1(sK2)),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f71,plain,(
% 0.97/0.63    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f30])).
% 0.97/0.63  fof(f30,plain,(
% 0.97/0.63    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.97/0.63    inference(flattening,[],[f29])).
% 0.97/0.63  fof(f29,plain,(
% 0.97/0.63    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.97/0.63    inference(ennf_transformation,[],[f8])).
% 0.97/0.63  fof(f8,axiom,(
% 0.97/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.97/0.63  fof(f293,plain,(
% 0.97/0.63    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.97/0.63    inference(forward_demodulation,[],[f292,f214])).
% 0.97/0.63  fof(f292,plain,(
% 0.97/0.63    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.97/0.63    inference(subsumption_resolution,[],[f291,f267])).
% 0.97/0.63  fof(f267,plain,(
% 0.97/0.63    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_5),
% 0.97/0.63    inference(forward_demodulation,[],[f266,f147])).
% 0.97/0.63  fof(f147,plain,(
% 0.97/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.97/0.63    inference(subsumption_resolution,[],[f146,f130])).
% 0.97/0.63  fof(f146,plain,(
% 0.97/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f144,f58])).
% 0.97/0.63  fof(f144,plain,(
% 0.97/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.97/0.63    inference(resolution,[],[f73,f62])).
% 0.97/0.63  fof(f73,plain,(
% 0.97/0.63    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f32])).
% 0.97/0.63  fof(f32,plain,(
% 0.97/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.97/0.63    inference(flattening,[],[f31])).
% 0.97/0.63  fof(f31,plain,(
% 0.97/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.97/0.63    inference(ennf_transformation,[],[f6])).
% 0.97/0.63  fof(f6,axiom,(
% 0.97/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.97/0.63  fof(f266,plain,(
% 0.97/0.63    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_5),
% 0.97/0.63    inference(forward_demodulation,[],[f254,f214])).
% 0.97/0.63  fof(f254,plain,(
% 0.97/0.63    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.97/0.63    inference(resolution,[],[f197,f83])).
% 0.97/0.63  fof(f83,plain,(
% 0.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f41])).
% 0.97/0.63  fof(f41,plain,(
% 0.97/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.97/0.63    inference(ennf_transformation,[],[f10])).
% 0.97/0.63  fof(f10,axiom,(
% 0.97/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.97/0.63  fof(f197,plain,(
% 0.97/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.97/0.63    inference(forward_demodulation,[],[f196,f95])).
% 0.97/0.63  fof(f196,plain,(
% 0.97/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))),
% 0.97/0.63    inference(forward_demodulation,[],[f195,f94])).
% 0.97/0.63  fof(f195,plain,(
% 0.97/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.97/0.63    inference(subsumption_resolution,[],[f194,f95])).
% 0.97/0.63  fof(f194,plain,(
% 0.97/0.63    u1_struct_0(sK1) != k2_struct_0(sK1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.97/0.63    inference(forward_demodulation,[],[f193,f61])).
% 0.97/0.63  fof(f61,plain,(
% 0.97/0.63    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.97/0.63    inference(cnf_transformation,[],[f52])).
% 0.97/0.63  fof(f193,plain,(
% 0.97/0.63    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.97/0.63    inference(subsumption_resolution,[],[f192,f58])).
% 0.97/0.63  fof(f192,plain,(
% 0.97/0.63    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f191,f59])).
% 0.97/0.63  fof(f191,plain,(
% 0.97/0.63    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.63    inference(subsumption_resolution,[],[f190,f62])).
% 0.97/0.63  fof(f190,plain,(
% 0.97/0.63    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.63    inference(resolution,[],[f87,f60])).
% 0.97/0.63  fof(f87,plain,(
% 0.97/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f44])).
% 0.97/0.63  fof(f44,plain,(
% 0.97/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.97/0.63    inference(flattening,[],[f43])).
% 0.97/0.63  fof(f43,plain,(
% 0.97/0.63    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.97/0.63    inference(ennf_transformation,[],[f14])).
% 0.97/0.63  fof(f14,axiom,(
% 0.97/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.97/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.97/0.63  fof(f291,plain,(
% 0.97/0.63    k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5)),
% 0.97/0.63    inference(forward_demodulation,[],[f290,f214])).
% 0.97/0.63  fof(f290,plain,(
% 0.97/0.63    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~spl3_4),
% 0.97/0.63    inference(subsumption_resolution,[],[f289,f131])).
% 0.97/0.63  fof(f131,plain,(
% 0.97/0.63    v1_funct_1(k2_funct_1(sK2))),
% 0.97/0.63    inference(subsumption_resolution,[],[f125,f130])).
% 0.97/0.63  fof(f125,plain,(
% 0.97/0.63    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.97/0.63    inference(resolution,[],[f70,f58])).
% 0.97/0.63  fof(f70,plain,(
% 0.97/0.63    ( ! [X0] : (~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.97/0.63    inference(cnf_transformation,[],[f28])).
% 0.97/0.63  fof(f28,plain,(
% 0.97/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.97/0.63    inference(flattening,[],[f27])).
% 0.97/0.63  fof(f27,plain,(
% 0.97/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.97/0.63    inference(ennf_transformation,[],[f3])).
% 0.97/0.64  fof(f3,axiom,(
% 0.97/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.97/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.97/0.64  fof(f289,plain,(
% 0.97/0.64    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.97/0.64    inference(subsumption_resolution,[],[f288,f189])).
% 0.97/0.64  fof(f189,plain,(
% 0.97/0.64    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.97/0.64    inference(forward_demodulation,[],[f188,f95])).
% 0.97/0.64  fof(f188,plain,(
% 0.97/0.64    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0))),
% 0.97/0.64    inference(forward_demodulation,[],[f187,f94])).
% 0.97/0.64  fof(f187,plain,(
% 0.97/0.64    v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.97/0.64    inference(subsumption_resolution,[],[f186,f95])).
% 0.97/0.64  fof(f186,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.97/0.64    inference(forward_demodulation,[],[f185,f61])).
% 0.97/0.64  fof(f185,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.97/0.64    inference(subsumption_resolution,[],[f184,f58])).
% 0.97/0.64  fof(f184,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f183,f59])).
% 0.97/0.64  fof(f183,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f182,f62])).
% 0.97/0.64  fof(f182,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.64    inference(resolution,[],[f86,f60])).
% 0.97/0.64  fof(f86,plain,(
% 0.97/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f44])).
% 0.97/0.64  fof(f288,plain,(
% 0.97/0.64    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.97/0.64    inference(subsumption_resolution,[],[f259,f249])).
% 0.97/0.64  fof(f249,plain,(
% 0.97/0.64    v2_funct_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.97/0.64    inference(subsumption_resolution,[],[f248,f123])).
% 0.97/0.64  fof(f123,plain,(
% 0.97/0.64    v1_relat_1(k2_funct_1(sK2)) | ~spl3_4),
% 0.97/0.64    inference(avatar_component_clause,[],[f121])).
% 0.97/0.64  fof(f121,plain,(
% 0.97/0.64    spl3_4 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.97/0.64  fof(f248,plain,(
% 0.97/0.64    v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f247,f131])).
% 0.97/0.64  fof(f247,plain,(
% 0.97/0.64    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f246,f130])).
% 0.97/0.64  fof(f246,plain,(
% 0.97/0.64    v2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f245,f58])).
% 0.97/0.64  fof(f245,plain,(
% 0.97/0.64    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f244,f142])).
% 0.97/0.64  fof(f142,plain,(
% 0.97/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f141,f130])).
% 0.97/0.64  fof(f141,plain,(
% 0.97/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f139,f58])).
% 0.97/0.64  fof(f139,plain,(
% 0.97/0.64    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.97/0.64    inference(resolution,[],[f72,f62])).
% 0.97/0.64  fof(f72,plain,(
% 0.97/0.64    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f32])).
% 0.97/0.64  fof(f244,plain,(
% 0.97/0.64    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f242,f65])).
% 0.97/0.64  fof(f65,plain,(
% 0.97/0.64    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.97/0.64    inference(cnf_transformation,[],[f4])).
% 0.97/0.64  fof(f4,axiom,(
% 0.97/0.64    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.97/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.97/0.64  fof(f242,plain,(
% 0.97/0.64    ~v2_funct_1(k6_relat_1(k1_relat_1(sK2))) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(superposition,[],[f77,f155])).
% 0.97/0.64  fof(f155,plain,(
% 0.97/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.97/0.64    inference(subsumption_resolution,[],[f154,f130])).
% 0.97/0.64  fof(f154,plain,(
% 0.97/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f152,f58])).
% 0.97/0.64  fof(f152,plain,(
% 0.97/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.97/0.64    inference(resolution,[],[f74,f62])).
% 0.97/0.64  fof(f74,plain,(
% 0.97/0.64    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f34])).
% 0.97/0.64  fof(f34,plain,(
% 0.97/0.64    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.97/0.64    inference(flattening,[],[f33])).
% 0.97/0.64  fof(f33,plain,(
% 0.97/0.64    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.97/0.64    inference(ennf_transformation,[],[f7])).
% 0.97/0.64  fof(f7,axiom,(
% 0.97/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.97/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.97/0.64  fof(f77,plain,(
% 0.97/0.64    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f36])).
% 0.97/0.64  fof(f36,plain,(
% 0.97/0.64    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.97/0.64    inference(flattening,[],[f35])).
% 0.97/0.64  fof(f35,plain,(
% 0.97/0.64    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.97/0.64    inference(ennf_transformation,[],[f5])).
% 0.97/0.64  fof(f5,axiom,(
% 0.97/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.97/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.97/0.64  fof(f259,plain,(
% 0.97/0.64    ~v2_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(sK2))),
% 0.97/0.64    inference(resolution,[],[f197,f88])).
% 0.97/0.64  fof(f88,plain,(
% 0.97/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f46])).
% 0.97/0.64  fof(f46,plain,(
% 0.97/0.64    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.97/0.64    inference(flattening,[],[f45])).
% 0.97/0.64  fof(f45,plain,(
% 0.97/0.64    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.97/0.64    inference(ennf_transformation,[],[f17])).
% 0.97/0.64  fof(f17,axiom,(
% 0.97/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.97/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.97/0.64  fof(f358,plain,(
% 0.97/0.64    ~r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | ~spl3_5),
% 0.97/0.64    inference(forward_demodulation,[],[f353,f214])).
% 0.97/0.64  fof(f353,plain,(
% 0.97/0.64    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK2)),
% 0.97/0.64    inference(superposition,[],[f100,f211])).
% 0.97/0.64  fof(f211,plain,(
% 0.97/0.64    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.97/0.64    inference(forward_demodulation,[],[f210,f94])).
% 0.97/0.64  fof(f210,plain,(
% 0.97/0.64    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.97/0.64    inference(forward_demodulation,[],[f209,f95])).
% 0.97/0.64  fof(f209,plain,(
% 0.97/0.64    k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f208,f95])).
% 0.97/0.64  fof(f208,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.97/0.64    inference(forward_demodulation,[],[f207,f61])).
% 0.97/0.64  fof(f207,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f206,f58])).
% 0.97/0.64  fof(f206,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f205,f59])).
% 0.97/0.64  fof(f205,plain,(
% 0.97/0.64    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.64    inference(subsumption_resolution,[],[f204,f62])).
% 0.97/0.64  fof(f204,plain,(
% 0.97/0.64    ~v2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 0.97/0.64    inference(resolution,[],[f88,f60])).
% 0.97/0.64  fof(f100,plain,(
% 0.97/0.64    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.97/0.64    inference(forward_demodulation,[],[f96,f95])).
% 0.97/0.64  fof(f96,plain,(
% 0.97/0.64    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.97/0.64    inference(superposition,[],[f63,f94])).
% 0.97/0.64  fof(f63,plain,(
% 0.97/0.64    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.97/0.64    inference(cnf_transformation,[],[f52])).
% 0.97/0.64  fof(f175,plain,(
% 0.97/0.64    spl3_5 | spl3_6),
% 0.97/0.64    inference(avatar_split_clause,[],[f166,f172,f168])).
% 0.97/0.64  fof(f166,plain,(
% 0.97/0.64    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.97/0.64    inference(forward_demodulation,[],[f165,f95])).
% 0.97/0.64  fof(f165,plain,(
% 0.97/0.64    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.97/0.64    inference(forward_demodulation,[],[f164,f94])).
% 0.97/0.64  fof(f164,plain,(
% 0.97/0.64    v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.97/0.64    inference(subsumption_resolution,[],[f163,f58])).
% 0.97/0.64  fof(f163,plain,(
% 0.97/0.64    ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.97/0.64    inference(subsumption_resolution,[],[f162,f59])).
% 0.97/0.64  fof(f162,plain,(
% 0.97/0.64    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | v1_partfun1(sK2,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1))),
% 0.97/0.64    inference(resolution,[],[f80,f60])).
% 0.97/0.64  fof(f80,plain,(
% 0.97/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f38])).
% 0.97/0.64  fof(f38,plain,(
% 0.97/0.64    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.97/0.64    inference(flattening,[],[f37])).
% 0.97/0.64  fof(f37,plain,(
% 0.97/0.64    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.97/0.64    inference(ennf_transformation,[],[f11])).
% 0.97/0.64  fof(f11,axiom,(
% 0.97/0.64    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.97/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.97/0.64  fof(f129,plain,(
% 0.97/0.64    spl3_3),
% 0.97/0.64    inference(avatar_contradiction_clause,[],[f128])).
% 0.97/0.64  fof(f128,plain,(
% 0.97/0.64    $false | spl3_3),
% 0.97/0.64    inference(subsumption_resolution,[],[f127,f78])).
% 0.97/0.64  fof(f127,plain,(
% 0.97/0.64    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | spl3_3),
% 0.97/0.64    inference(subsumption_resolution,[],[f126,f119])).
% 0.97/0.64  fof(f119,plain,(
% 0.97/0.64    ~v1_relat_1(sK2) | spl3_3),
% 0.97/0.64    inference(avatar_component_clause,[],[f117])).
% 0.97/0.64  fof(f117,plain,(
% 0.97/0.64    spl3_3 <=> v1_relat_1(sK2)),
% 0.97/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.97/0.64  fof(f124,plain,(
% 0.97/0.64    ~spl3_3 | spl3_4),
% 0.97/0.64    inference(avatar_split_clause,[],[f115,f121,f117])).
% 0.97/0.64  fof(f115,plain,(
% 0.97/0.64    v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 0.97/0.64    inference(resolution,[],[f69,f58])).
% 0.97/0.64  fof(f69,plain,(
% 0.97/0.64    ( ! [X0] : (~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.97/0.64    inference(cnf_transformation,[],[f28])).
% 0.97/0.64  % SZS output end Proof for theBenchmark
% 0.97/0.64  % (31510)------------------------------
% 0.97/0.64  % (31510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.97/0.64  % (31510)Termination reason: Refutation
% 0.97/0.64  
% 0.97/0.64  % (31510)Memory used [KB]: 10746
% 0.97/0.64  % (31510)Time elapsed: 0.067 s
% 0.97/0.64  % (31510)------------------------------
% 0.97/0.64  % (31510)------------------------------
% 0.97/0.64  % (31365)Success in time 0.279 s
%------------------------------------------------------------------------------
