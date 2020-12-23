%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  301 (3232 expanded)
%              Number of leaves         :   39 (1085 expanded)
%              Depth                    :   29
%              Number of atoms          : 1233 (21160 expanded)
%              Number of equality atoms :  181 (3263 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1808,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f136,f148,f189,f262,f298,f402,f489,f570,f998,f1015,f1040,f1086,f1148,f1221,f1237,f1328,f1330,f1713,f1744,f1785,f1807])).

fof(f1807,plain,
    ( ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_54 ),
    inference(avatar_contradiction_clause,[],[f1806])).

fof(f1806,plain,
    ( $false
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_54 ),
    inference(subsumption_resolution,[],[f1804,f1359])).

fof(f1359,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1358,f403])).

fof(f403,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f58,f293])).

fof(f293,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl3_16
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
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
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
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
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
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
          & l1_struct_0(X1) )
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
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
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

fof(f1358,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1349,f1195])).

fof(f1195,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(backward_demodulation,[],[f1111,f1134])).

fof(f1134,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f1132,plain,
    ( spl3_40
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f1111,plain,
    ( v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0))
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f815,f293])).

fof(f815,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f150,f380])).

fof(f380,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f150,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f149,f109])).

fof(f109,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f57,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f149,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f59,f108])).

% (18861)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f108,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f56,f64])).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f1349,plain,
    ( r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(resolution,[],[f1338,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_funct_2(X0,X1,X3,X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f1338,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f1116,f1134])).

fof(f1116,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0))))
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f814,f293])).

fof(f814,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f152,f380])).

fof(f152,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f151,f108])).

fof(f151,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f60,f109])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f1804,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_54 ),
    inference(backward_demodulation,[],[f1424,f1626])).

fof(f1626,plain,
    ( k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f1624])).

fof(f1624,plain,
    ( spl3_54
  <=> k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f1424,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40
    | ~ spl3_43 ),
    inference(backward_demodulation,[],[f1381,f1220])).

fof(f1220,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f1218])).

fof(f1218,plain,
    ( spl3_43
  <=> k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f1381,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f1192,f1134])).

fof(f1192,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f895,f293])).

fof(f895,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f812,f380])).

fof(f812,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f359,f108])).

fof(f359,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(forward_demodulation,[],[f63,f109])).

fof(f63,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f1785,plain,
    ( spl3_12
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(avatar_contradiction_clause,[],[f1784])).

fof(f1784,plain,
    ( $false
    | spl3_12
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1783,f1338])).

fof(f1783,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_12
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f249,f293])).

fof(f249,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1744,plain,
    ( ~ spl3_6
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_45
    | spl3_55 ),
    inference(avatar_contradiction_clause,[],[f1743])).

fof(f1743,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_45
    | spl3_55 ),
    inference(subsumption_resolution,[],[f1742,f410])).

fof(f410,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f147,f293])).

fof(f147,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_6
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f1742,plain,
    ( ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_45
    | spl3_55 ),
    inference(subsumption_resolution,[],[f1741,f1282])).

fof(f1282,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f261,f293])).

fof(f261,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f259])).

fof(f259,plain,
    ( spl3_14
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1741,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_45
    | spl3_55 ),
    inference(subsumption_resolution,[],[f1740,f1236])).

fof(f1236,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f1234])).

fof(f1234,plain,
    ( spl3_45
  <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f1740,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | spl3_55 ),
    inference(resolution,[],[f1712,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f1712,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | spl3_55 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f1710,plain,
    ( spl3_55
  <=> v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f1713,plain,
    ( spl3_54
    | ~ spl3_55
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_16
    | spl3_17
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f1708,f1234,f295,f291,f259,f145,f1710,f1624])).

fof(f295,plain,
    ( spl3_17
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1708,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_16
    | spl3_17
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1698,f296])).

fof(f296,plain,
    ( k1_xboole_0 != k2_struct_0(sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f295])).

fof(f1698,plain,
    ( ~ v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_45 ),
    inference(resolution,[],[f1466,f100])).

fof(f100,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1466,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_6
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1465,f410])).

fof(f1465,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f1452,f1282])).

fof(f1452,plain,
    ( m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k2_funct_1(k1_xboole_0))
    | ~ spl3_45 ),
    inference(resolution,[],[f1236,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1330,plain,
    ( spl3_9
    | ~ spl3_16
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f1329])).

fof(f1329,plain,
    ( $false
    | spl3_9
    | ~ spl3_16
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f1147,f1167])).

fof(f1167,plain,
    ( ~ v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | spl3_9
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f182,f293])).

fof(f182,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_9
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1147,plain,
    ( v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f1145])).

fof(f1145,plain,
    ( spl3_41
  <=> v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f1328,plain,
    ( ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f1327])).

fof(f1327,plain,
    ( $false
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40
    | spl3_42 ),
    inference(subsumption_resolution,[],[f1216,f1194])).

fof(f1194,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(backward_demodulation,[],[f1116,f1134])).

fof(f1216,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f1214])).

fof(f1214,plain,
    ( spl3_42
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f1237,plain,
    ( ~ spl3_42
    | spl3_45
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f1232,f1132,f379,f291,f1234,f1214])).

fof(f1232,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1231,f403])).

fof(f1231,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1230,f1195])).

fof(f1230,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1206,f404])).

fof(f404,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f62,f293])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f1206,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(trivial_inequality_removal,[],[f1205])).

fof(f1205,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
    | ~ v2_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(superposition,[],[f91,f1193])).

fof(f1193,plain,
    ( k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(backward_demodulation,[],[f1168,f1134])).

fof(f1168,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f813,f293])).

fof(f813,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f192,f380])).

fof(f192,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f191,f108])).

fof(f191,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f61,f109])).

fof(f61,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f1221,plain,
    ( ~ spl3_42
    | spl3_43
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f1212,f1132,f379,f291,f1218,f1214])).

fof(f1212,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1211,f403])).

fof(f1211,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1210,f1195])).

fof(f1210,plain,
    ( k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1209,f404])).

fof(f1209,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(trivial_inequality_removal,[],[f1202])).

fof(f1202,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v2_funct_1(k1_xboole_0)
    | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19
    | ~ spl3_40 ),
    inference(superposition,[],[f92,f1193])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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

fof(f1148,plain,
    ( spl3_41
    | spl3_40
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f1143,f379,f291,f1132,f1145])).

fof(f1143,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1142,f403])).

fof(f1142,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f1123,f1111])).

fof(f1123,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | v1_partfun1(k1_xboole_0,k2_struct_0(sK0))
    | ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f1116,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f1086,plain,
    ( ~ spl3_8
    | spl3_9
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f1085])).

fof(f1085,plain,
    ( $false
    | ~ spl3_8
    | spl3_9
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f1083,f518])).

fof(f518,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f517,f58])).

fof(f517,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(subsumption_resolution,[],[f505,f494])).

fof(f494,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f493,f297])).

fof(f297,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f295])).

fof(f493,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f150,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl3_8
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f505,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(resolution,[],[f496,f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f496,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_8
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f492,f297])).

fof(f492,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f152,f170])).

fof(f1083,plain,
    ( ~ v1_partfun1(sK2,k1_xboole_0)
    | spl3_9
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f182,f297])).

fof(f1040,plain,
    ( ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f1039])).

fof(f1039,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f1037,f856])).

fof(f856,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f855,f58])).

fof(f855,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f845,f821])).

fof(f821,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f815,f770])).

fof(f770,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f769,f118])).

fof(f118,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f769,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f768,f154])).

fof(f154,plain,(
    v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f152,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f768,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f183,f76])).

fof(f76,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f183,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f181])).

fof(f845,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(resolution,[],[f829,f107])).

fof(f829,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f814,f770])).

fof(f1037,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f934,f997])).

fof(f997,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f995])).

fof(f995,plain,
    ( spl3_33
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f934,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(backward_demodulation,[],[f896,f880])).

fof(f880,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f879,f58])).

fof(f879,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f878,f821])).

fof(f878,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f877,f829])).

fof(f877,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f876,f62])).

fof(f876,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f869])).

fof(f869,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(superposition,[],[f92,f863])).

fof(f863,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f813,f770])).

fof(f896,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f895,f770])).

fof(f1015,plain,
    ( ~ spl3_1
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f1014])).

fof(f1014,plain,
    ( $false
    | ~ spl3_1
    | spl3_32 ),
    inference(subsumption_resolution,[],[f1013,f118])).

fof(f1013,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_32 ),
    inference(subsumption_resolution,[],[f1012,f58])).

fof(f1012,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_32 ),
    inference(subsumption_resolution,[],[f1011,f62])).

fof(f1011,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_32 ),
    inference(resolution,[],[f993,f68])).

fof(f68,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f993,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f991])).

fof(f991,plain,
    ( spl3_32
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f998,plain,
    ( ~ spl3_32
    | spl3_33
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f989,f379,f181,f145,f133,f127,f117,f995,f991])).

fof(f127,plain,
    ( spl3_3
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f133,plain,
    ( spl3_4
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f989,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f988,f135])).

fof(f135,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f988,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f987,f147])).

fof(f987,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f986,f862])).

fof(f862,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f861,f380])).

fof(f861,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f208,f770])).

fof(f208,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f207,f58])).

fof(f207,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f206,f150])).

fof(f206,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f205,f152])).

fof(f205,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f198,f62])).

fof(f198,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f195])).

fof(f195,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f90,f192])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f986,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f985,f888])).

fof(f888,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f887,f58])).

fof(f887,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f886,f821])).

fof(f886,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f885,f829])).

fof(f885,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f873,f62])).

fof(f873,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f872])).

fof(f872,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(superposition,[],[f91,f863])).

fof(f985,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(trivial_inequality_removal,[],[f978])).

fof(f978,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(superposition,[],[f92,f946])).

fof(f946,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f937,f129])).

fof(f129,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f937,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_9
    | ~ spl3_19 ),
    inference(resolution,[],[f888,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f570,plain,
    ( ~ spl3_8
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | ~ spl3_8
    | spl3_19 ),
    inference(subsumption_resolution,[],[f568,f170])).

fof(f568,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | ~ spl3_8
    | spl3_19 ),
    inference(forward_demodulation,[],[f381,f299])).

fof(f299,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f280,f213])).

fof(f213,plain,
    ( k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f192,f170])).

fof(f280,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f214,f78])).

fof(f214,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f152,f170])).

fof(f381,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | spl3_19 ),
    inference(avatar_component_clause,[],[f379])).

fof(f489,plain,
    ( spl3_9
    | spl3_8 ),
    inference(avatar_split_clause,[],[f488,f168,f181])).

fof(f488,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f487,f58])).

fof(f487,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f476,f150])).

fof(f476,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f152,f106])).

fof(f402,plain,
    ( ~ spl3_1
    | ~ spl3_9
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_9
    | spl3_19 ),
    inference(subsumption_resolution,[],[f381,f365])).

fof(f365,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f341,f321])).

fof(f321,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(resolution,[],[f317,f78])).

fof(f317,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f152,f310])).

fof(f310,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f309,f118])).

fof(f309,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f308,f154])).

fof(f308,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f183,f76])).

fof(f341,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f192,f310])).

fof(f298,plain,
    ( spl3_16
    | spl3_17
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f289,f168,f295,f291])).

fof(f289,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f279,f215])).

fof(f215,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f150,f170])).

fof(f279,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(resolution,[],[f214,f100])).

fof(f262,plain,
    ( ~ spl3_12
    | spl3_14
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f257,f168,f259,f247])).

fof(f257,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f256,f58])).

fof(f256,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f255,f215])).

fof(f255,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f240,f62])).

fof(f240,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f237])).

fof(f237,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_8 ),
    inference(superposition,[],[f90,f213])).

fof(f189,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f188])).

fof(f188,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f187,f75])).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f187,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f161,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f161,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(resolution,[],[f152,f65])).

fof(f65,plain,(
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

fof(f148,plain,
    ( ~ spl3_1
    | spl3_6 ),
    inference(avatar_split_clause,[],[f143,f145,f117])).

fof(f143,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f114,f58])).

fof(f114,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f136,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_split_clause,[],[f131,f133,f117])).

fof(f131,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f112,f58])).

fof(f112,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f72])).

fof(f72,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f130,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f125,f127,f117])).

fof(f125,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f111,f58])).

fof(f111,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f74])).

fof(f74,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (18868)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.48  % (18857)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (18856)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (18854)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.53  % (18849)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.53  % (18873)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (18874)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (18869)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (18860)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.54  % (18866)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.54  % (18870)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (18855)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.55  % (18862)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.55  % (18850)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (18851)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.56  % (18872)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.56  % (18852)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.56  % (18864)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.57  % (18863)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.57  % (18865)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.57  % (18853)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.58  % (18875)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.58  % (18876)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.58  % (18867)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.58  % (18871)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.58  % (18850)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1808,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f130,f136,f148,f189,f262,f298,f402,f489,f570,f998,f1015,f1040,f1086,f1148,f1221,f1237,f1328,f1330,f1713,f1744,f1785,f1807])).
% 0.20/0.58  fof(f1807,plain,(
% 0.20/0.58    ~spl3_16 | ~spl3_19 | ~spl3_40 | ~spl3_43 | ~spl3_54),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1806])).
% 0.20/0.58  fof(f1806,plain,(
% 0.20/0.58    $false | (~spl3_16 | ~spl3_19 | ~spl3_40 | ~spl3_43 | ~spl3_54)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1804,f1359])).
% 0.20/0.58  fof(f1359,plain,(
% 0.20/0.58    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1358,f403])).
% 0.20/0.58  fof(f403,plain,(
% 0.20/0.58    v1_funct_1(k1_xboole_0) | ~spl3_16),
% 0.20/0.58    inference(backward_demodulation,[],[f58,f293])).
% 0.20/0.58  fof(f293,plain,(
% 0.20/0.58    k1_xboole_0 = sK2 | ~spl3_16),
% 0.20/0.58    inference(avatar_component_clause,[],[f291])).
% 0.20/0.58  fof(f291,plain,(
% 0.20/0.58    spl3_16 <=> k1_xboole_0 = sK2),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    v1_funct_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f19])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.58    inference(pure_predicate_removal,[],[f18])).
% 0.20/0.58  fof(f18,negated_conjecture,(
% 0.20/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.58    inference(negated_conjecture,[],[f17])).
% 0.20/0.58  fof(f17,conjecture,(
% 0.20/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.20/0.58  fof(f1358,plain,(
% 0.20/0.58    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1349,f1195])).
% 0.20/0.58  fof(f1195,plain,(
% 0.20/0.58    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(backward_demodulation,[],[f1111,f1134])).
% 0.20/0.58  fof(f1134,plain,(
% 0.20/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl3_40),
% 0.20/0.58    inference(avatar_component_clause,[],[f1132])).
% 0.20/0.58  fof(f1132,plain,(
% 0.20/0.58    spl3_40 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.58  fof(f1111,plain,(
% 0.20/0.58    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0)) | (~spl3_16 | ~spl3_19)),
% 0.20/0.58    inference(backward_demodulation,[],[f815,f293])).
% 0.20/0.58  fof(f815,plain,(
% 0.20/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_19),
% 0.20/0.58    inference(backward_demodulation,[],[f150,f380])).
% 0.20/0.58  fof(f380,plain,(
% 0.20/0.58    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_19),
% 0.20/0.58    inference(avatar_component_clause,[],[f379])).
% 0.20/0.58  fof(f379,plain,(
% 0.20/0.58    spl3_19 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.58  fof(f150,plain,(
% 0.20/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.58    inference(forward_demodulation,[],[f149,f109])).
% 0.20/0.58  fof(f109,plain,(
% 0.20/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.58    inference(resolution,[],[f57,f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    l1_struct_0(sK1)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f149,plain,(
% 0.20/0.58    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.58    inference(backward_demodulation,[],[f59,f108])).
% 0.20/0.58  % (18861)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.58    inference(resolution,[],[f56,f64])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    l1_struct_0(sK0)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f59,plain,(
% 0.20/0.58    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f1349,plain,(
% 0.20/0.58    r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(resolution,[],[f1338,f107])).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_funct_2(X0,X1,X3,X3) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f104])).
% 0.20/0.58  fof(f104,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.20/0.58    inference(equality_resolution,[],[f96])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f48])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.20/0.58  fof(f1338,plain,(
% 0.20/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(forward_demodulation,[],[f1116,f1134])).
% 0.20/0.58  fof(f1116,plain,(
% 0.20/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0)))) | (~spl3_16 | ~spl3_19)),
% 0.20/0.58    inference(forward_demodulation,[],[f814,f293])).
% 0.20/0.58  fof(f814,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_19),
% 0.20/0.58    inference(backward_demodulation,[],[f152,f380])).
% 0.20/0.58  fof(f152,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.58    inference(forward_demodulation,[],[f151,f108])).
% 0.20/0.58  fof(f151,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.58    inference(forward_demodulation,[],[f60,f109])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f1804,plain,(
% 0.20/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40 | ~spl3_43 | ~spl3_54)),
% 0.20/0.58    inference(backward_demodulation,[],[f1424,f1626])).
% 0.20/0.58  fof(f1626,plain,(
% 0.20/0.58    k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | ~spl3_54),
% 0.20/0.58    inference(avatar_component_clause,[],[f1624])).
% 0.20/0.58  fof(f1624,plain,(
% 0.20/0.58    spl3_54 <=> k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.58  fof(f1424,plain,(
% 0.20/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40 | ~spl3_43)),
% 0.20/0.58    inference(backward_demodulation,[],[f1381,f1220])).
% 0.20/0.58  fof(f1220,plain,(
% 0.20/0.58    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~spl3_43),
% 0.20/0.58    inference(avatar_component_clause,[],[f1218])).
% 0.20/0.58  fof(f1218,plain,(
% 0.20/0.58    spl3_43 <=> k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.58  fof(f1381,plain,(
% 0.20/0.58    ~r2_funct_2(k2_struct_0(sK0),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(forward_demodulation,[],[f1192,f1134])).
% 0.20/0.58  fof(f1192,plain,(
% 0.20/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k2_tops_2(k2_relat_1(k1_xboole_0),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0)),k1_xboole_0) | (~spl3_16 | ~spl3_19)),
% 0.20/0.58    inference(forward_demodulation,[],[f895,f293])).
% 0.20/0.58  fof(f895,plain,(
% 0.20/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~spl3_19),
% 0.20/0.58    inference(forward_demodulation,[],[f812,f380])).
% 0.20/0.58  fof(f812,plain,(
% 0.20/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.58    inference(forward_demodulation,[],[f359,f108])).
% 0.20/0.58  fof(f359,plain,(
% 0.20/0.58    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.20/0.58    inference(forward_demodulation,[],[f63,f109])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f1785,plain,(
% 0.20/0.58    spl3_12 | ~spl3_16 | ~spl3_19 | ~spl3_40),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1784])).
% 0.20/0.58  fof(f1784,plain,(
% 0.20/0.58    $false | (spl3_12 | ~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1783,f1338])).
% 0.20/0.58  fof(f1783,plain,(
% 0.20/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (spl3_12 | ~spl3_16)),
% 0.20/0.58    inference(forward_demodulation,[],[f249,f293])).
% 0.20/0.58  fof(f249,plain,(
% 0.20/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | spl3_12),
% 0.20/0.58    inference(avatar_component_clause,[],[f247])).
% 0.20/0.58  fof(f247,plain,(
% 0.20/0.58    spl3_12 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.58  fof(f1744,plain,(
% 0.20/0.58    ~spl3_6 | ~spl3_14 | ~spl3_16 | ~spl3_45 | spl3_55),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1743])).
% 0.20/0.58  fof(f1743,plain,(
% 0.20/0.58    $false | (~spl3_6 | ~spl3_14 | ~spl3_16 | ~spl3_45 | spl3_55)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1742,f410])).
% 0.20/0.58  fof(f410,plain,(
% 0.20/0.58    v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_16)),
% 0.20/0.58    inference(backward_demodulation,[],[f147,f293])).
% 0.20/0.58  fof(f147,plain,(
% 0.20/0.58    v1_funct_1(k2_funct_1(sK2)) | ~spl3_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f145])).
% 0.20/0.58  fof(f145,plain,(
% 0.20/0.58    spl3_6 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.58  fof(f1742,plain,(
% 0.20/0.58    ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_14 | ~spl3_16 | ~spl3_45 | spl3_55)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1741,f1282])).
% 0.20/0.58  fof(f1282,plain,(
% 0.20/0.58    v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | (~spl3_14 | ~spl3_16)),
% 0.20/0.58    inference(forward_demodulation,[],[f261,f293])).
% 0.20/0.58  fof(f261,plain,(
% 0.20/0.58    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~spl3_14),
% 0.20/0.58    inference(avatar_component_clause,[],[f259])).
% 0.20/0.58  fof(f259,plain,(
% 0.20/0.58    spl3_14 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.58  fof(f1741,plain,(
% 0.20/0.58    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_45 | spl3_55)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1740,f1236])).
% 0.20/0.58  fof(f1236,plain,(
% 0.20/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~spl3_45),
% 0.20/0.58    inference(avatar_component_clause,[],[f1234])).
% 0.20/0.58  fof(f1234,plain,(
% 0.20/0.58    spl3_45 <=> m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.58  fof(f1740,plain,(
% 0.20/0.58    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | spl3_55),
% 0.20/0.58    inference(resolution,[],[f1712,f87])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f39])).
% 0.20/0.58  fof(f39,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f16])).
% 0.20/0.58  fof(f16,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.58  fof(f1712,plain,(
% 0.20/0.58    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | spl3_55),
% 0.20/0.58    inference(avatar_component_clause,[],[f1710])).
% 0.20/0.58  fof(f1710,plain,(
% 0.20/0.58    spl3_55 <=> v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.20/0.58  fof(f1713,plain,(
% 0.20/0.58    spl3_54 | ~spl3_55 | ~spl3_6 | ~spl3_14 | ~spl3_16 | spl3_17 | ~spl3_45),
% 0.20/0.58    inference(avatar_split_clause,[],[f1708,f1234,f295,f291,f259,f145,f1710,f1624])).
% 0.20/0.58  fof(f295,plain,(
% 0.20/0.58    spl3_17 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.58  fof(f1708,plain,(
% 0.20/0.58    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_14 | ~spl3_16 | spl3_17 | ~spl3_45)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1698,f296])).
% 0.20/0.58  fof(f296,plain,(
% 0.20/0.58    k1_xboole_0 != k2_struct_0(sK0) | spl3_17),
% 0.20/0.58    inference(avatar_component_clause,[],[f295])).
% 0.20/0.58  fof(f1698,plain,(
% 0.20/0.58    ~v1_funct_2(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)) | (~spl3_6 | ~spl3_14 | ~spl3_16 | ~spl3_45)),
% 0.20/0.58    inference(resolution,[],[f1466,f100])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.58    inference(equality_resolution,[],[f84])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(nnf_transformation,[],[f38])).
% 0.20/0.58  fof(f38,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(flattening,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.58    inference(ennf_transformation,[],[f8])).
% 0.20/0.58  fof(f8,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.58  fof(f1466,plain,(
% 0.20/0.58    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_6 | ~spl3_14 | ~spl3_16 | ~spl3_45)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1465,f410])).
% 0.20/0.58  fof(f1465,plain,(
% 0.20/0.58    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | (~spl3_14 | ~spl3_16 | ~spl3_45)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1452,f1282])).
% 0.20/0.58  fof(f1452,plain,(
% 0.20/0.58    m1_subset_1(k2_tops_2(k1_xboole_0,k2_struct_0(sK0),k2_funct_1(k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k2_funct_1(k1_xboole_0)) | ~spl3_45),
% 0.20/0.58    inference(resolution,[],[f1236,f88])).
% 0.20/0.58  fof(f88,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f40])).
% 0.20/0.58  fof(f1330,plain,(
% 0.20/0.58    spl3_9 | ~spl3_16 | ~spl3_41),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1329])).
% 0.20/0.58  fof(f1329,plain,(
% 0.20/0.58    $false | (spl3_9 | ~spl3_16 | ~spl3_41)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1147,f1167])).
% 0.20/0.58  fof(f1167,plain,(
% 0.20/0.58    ~v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | (spl3_9 | ~spl3_16)),
% 0.20/0.58    inference(forward_demodulation,[],[f182,f293])).
% 0.20/0.58  fof(f182,plain,(
% 0.20/0.58    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f181])).
% 0.20/0.58  fof(f181,plain,(
% 0.20/0.58    spl3_9 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.58  fof(f1147,plain,(
% 0.20/0.58    v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | ~spl3_41),
% 0.20/0.58    inference(avatar_component_clause,[],[f1145])).
% 0.20/0.58  fof(f1145,plain,(
% 0.20/0.58    spl3_41 <=> v1_partfun1(k1_xboole_0,k2_struct_0(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.58  fof(f1328,plain,(
% 0.20/0.58    ~spl3_16 | ~spl3_19 | ~spl3_40 | spl3_42),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1327])).
% 0.20/0.58  fof(f1327,plain,(
% 0.20/0.58    $false | (~spl3_16 | ~spl3_19 | ~spl3_40 | spl3_42)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1216,f1194])).
% 0.20/0.58  fof(f1194,plain,(
% 0.20/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(backward_demodulation,[],[f1116,f1134])).
% 0.20/0.58  fof(f1216,plain,(
% 0.20/0.58    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | spl3_42),
% 0.20/0.58    inference(avatar_component_clause,[],[f1214])).
% 0.20/0.58  fof(f1214,plain,(
% 0.20/0.58    spl3_42 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.58  fof(f1237,plain,(
% 0.20/0.58    ~spl3_42 | spl3_45 | ~spl3_16 | ~spl3_19 | ~spl3_40),
% 0.20/0.58    inference(avatar_split_clause,[],[f1232,f1132,f379,f291,f1234,f1214])).
% 0.20/0.58  fof(f1232,plain,(
% 0.20/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1231,f403])).
% 0.20/0.58  fof(f1231,plain,(
% 0.20/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1230,f1195])).
% 0.20/0.58  fof(f1230,plain,(
% 0.20/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1206,f404])).
% 0.20/0.58  fof(f404,plain,(
% 0.20/0.58    v2_funct_1(k1_xboole_0) | ~spl3_16),
% 0.20/0.58    inference(backward_demodulation,[],[f62,f293])).
% 0.20/0.58  fof(f62,plain,(
% 0.20/0.58    v2_funct_1(sK2)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f1206,plain,(
% 0.20/0.58    m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v2_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f1205])).
% 1.75/0.58  fof(f1205,plain,(
% 1.75/0.58    k1_xboole_0 != k1_xboole_0 | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v2_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(superposition,[],[f91,f1193])).
% 1.75/0.58  fof(f1193,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(backward_demodulation,[],[f1168,f1134])).
% 1.75/0.58  fof(f1168,plain,(
% 1.75/0.58    k2_relat_1(k1_xboole_0) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl3_16 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f813,f293])).
% 1.75/0.58  fof(f813,plain,(
% 1.75/0.58    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_19),
% 1.75/0.58    inference(backward_demodulation,[],[f192,f380])).
% 1.75/0.58  fof(f192,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f191,f108])).
% 1.75/0.58  fof(f191,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.75/0.58    inference(forward_demodulation,[],[f61,f109])).
% 1.75/0.58  fof(f61,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f91,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f42])).
% 1.75/0.58  fof(f42,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f41])).
% 1.75/0.58  fof(f41,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f12])).
% 1.75/0.58  fof(f12,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.75/0.58  fof(f1221,plain,(
% 1.75/0.58    ~spl3_42 | spl3_43 | ~spl3_16 | ~spl3_19 | ~spl3_40),
% 1.75/0.58    inference(avatar_split_clause,[],[f1212,f1132,f379,f291,f1218,f1214])).
% 1.75/0.58  fof(f1212,plain,(
% 1.75/0.58    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1211,f403])).
% 1.75/0.58  fof(f1211,plain,(
% 1.75/0.58    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1210,f1195])).
% 1.75/0.58  fof(f1210,plain,(
% 1.75/0.58    k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1209,f404])).
% 1.75/0.58  fof(f1209,plain,(
% 1.75/0.58    ~v2_funct_1(k1_xboole_0) | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(trivial_inequality_removal,[],[f1202])).
% 1.75/0.58  fof(f1202,plain,(
% 1.75/0.58    k1_xboole_0 != k1_xboole_0 | ~v2_funct_1(k1_xboole_0) | k2_funct_1(k1_xboole_0) = k2_tops_2(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19 | ~spl3_40)),
% 1.75/0.58    inference(superposition,[],[f92,f1193])).
% 1.75/0.58  fof(f92,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f44])).
% 1.75/0.58  fof(f44,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f43])).
% 1.75/0.58  fof(f43,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f15])).
% 1.75/0.58  fof(f15,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 1.75/0.58  fof(f1148,plain,(
% 1.75/0.58    spl3_41 | spl3_40 | ~spl3_16 | ~spl3_19),
% 1.75/0.58    inference(avatar_split_clause,[],[f1143,f379,f291,f1132,f1145])).
% 1.75/0.58  fof(f1143,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | (~spl3_16 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1142,f403])).
% 1.75/0.58  fof(f1142,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1123,f1111])).
% 1.75/0.58  fof(f1123,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | v1_partfun1(k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k2_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | (~spl3_16 | ~spl3_19)),
% 1.75/0.58    inference(resolution,[],[f1116,f106])).
% 1.75/0.58  fof(f106,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(duplicate_literal_removal,[],[f93])).
% 1.75/0.58  fof(f93,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f46])).
% 1.75/0.58  fof(f46,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.75/0.58    inference(flattening,[],[f45])).
% 1.75/0.58  fof(f45,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.75/0.58    inference(ennf_transformation,[],[f11])).
% 1.75/0.58  fof(f11,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 1.75/0.58  fof(f1086,plain,(
% 1.75/0.58    ~spl3_8 | spl3_9 | ~spl3_17),
% 1.75/0.58    inference(avatar_contradiction_clause,[],[f1085])).
% 1.75/0.58  fof(f1085,plain,(
% 1.75/0.58    $false | (~spl3_8 | spl3_9 | ~spl3_17)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1083,f518])).
% 1.75/0.58  fof(f518,plain,(
% 1.75/0.58    v1_partfun1(sK2,k1_xboole_0) | (~spl3_8 | ~spl3_17)),
% 1.75/0.58    inference(subsumption_resolution,[],[f517,f58])).
% 1.75/0.58  fof(f517,plain,(
% 1.75/0.58    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | (~spl3_8 | ~spl3_17)),
% 1.75/0.58    inference(subsumption_resolution,[],[f505,f494])).
% 1.75/0.58  fof(f494,plain,(
% 1.75/0.58    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl3_8 | ~spl3_17)),
% 1.75/0.58    inference(backward_demodulation,[],[f493,f297])).
% 1.75/0.58  fof(f297,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_17),
% 1.75/0.58    inference(avatar_component_clause,[],[f295])).
% 1.75/0.58  fof(f493,plain,(
% 1.75/0.58    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_8),
% 1.75/0.58    inference(backward_demodulation,[],[f150,f170])).
% 1.75/0.58  fof(f170,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK1) | ~spl3_8),
% 1.75/0.58    inference(avatar_component_clause,[],[f168])).
% 1.75/0.58  fof(f168,plain,(
% 1.75/0.58    spl3_8 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.75/0.58  fof(f505,plain,(
% 1.75/0.58    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | (~spl3_8 | ~spl3_17)),
% 1.75/0.58    inference(resolution,[],[f496,f105])).
% 1.75/0.58  fof(f105,plain,(
% 1.75/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(duplicate_literal_removal,[],[f103])).
% 1.75/0.58  fof(f103,plain,(
% 1.75/0.58    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(equality_resolution,[],[f94])).
% 1.75/0.58  fof(f94,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f46])).
% 1.75/0.58  fof(f496,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl3_8 | ~spl3_17)),
% 1.75/0.58    inference(forward_demodulation,[],[f492,f297])).
% 1.75/0.58  fof(f492,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.75/0.58    inference(backward_demodulation,[],[f152,f170])).
% 1.75/0.58  fof(f1083,plain,(
% 1.75/0.58    ~v1_partfun1(sK2,k1_xboole_0) | (spl3_9 | ~spl3_17)),
% 1.75/0.58    inference(backward_demodulation,[],[f182,f297])).
% 1.75/0.58  fof(f1040,plain,(
% 1.75/0.58    ~spl3_1 | ~spl3_9 | ~spl3_19 | ~spl3_33),
% 1.75/0.58    inference(avatar_contradiction_clause,[],[f1039])).
% 1.75/0.58  fof(f1039,plain,(
% 1.75/0.58    $false | (~spl3_1 | ~spl3_9 | ~spl3_19 | ~spl3_33)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1037,f856])).
% 1.75/0.58  fof(f856,plain,(
% 1.75/0.58    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f855,f58])).
% 1.75/0.58  fof(f855,plain,(
% 1.75/0.58    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f845,f821])).
% 1.75/0.58  fof(f821,plain,(
% 1.75/0.58    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f815,f770])).
% 1.75/0.58  fof(f770,plain,(
% 1.75/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_1 | ~spl3_9)),
% 1.75/0.58    inference(subsumption_resolution,[],[f769,f118])).
% 1.75/0.58  fof(f118,plain,(
% 1.75/0.58    v1_relat_1(sK2) | ~spl3_1),
% 1.75/0.58    inference(avatar_component_clause,[],[f117])).
% 1.75/0.58  fof(f117,plain,(
% 1.75/0.58    spl3_1 <=> v1_relat_1(sK2)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.75/0.58  fof(f769,plain,(
% 1.75/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_9),
% 1.75/0.58    inference(subsumption_resolution,[],[f768,f154])).
% 1.75/0.58  fof(f154,plain,(
% 1.75/0.58    v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.75/0.58    inference(resolution,[],[f152,f79])).
% 1.75/0.58  fof(f79,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f36])).
% 1.75/0.58  fof(f36,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f20])).
% 1.75/0.58  fof(f20,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.75/0.58    inference(pure_predicate_removal,[],[f6])).
% 1.75/0.58  fof(f6,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.75/0.58  fof(f768,plain,(
% 1.75/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_9),
% 1.75/0.58    inference(resolution,[],[f183,f76])).
% 1.75/0.58  fof(f76,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f53])).
% 1.75/0.58  fof(f53,plain,(
% 1.75/0.58    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(nnf_transformation,[],[f34])).
% 1.75/0.58  fof(f34,plain,(
% 1.75/0.58    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(flattening,[],[f33])).
% 1.75/0.58  fof(f33,plain,(
% 1.75/0.58    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.75/0.58    inference(ennf_transformation,[],[f9])).
% 1.75/0.58  fof(f9,axiom,(
% 1.75/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 1.75/0.58  fof(f183,plain,(
% 1.75/0.58    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_9),
% 1.75/0.58    inference(avatar_component_clause,[],[f181])).
% 1.75/0.58  fof(f845,plain,(
% 1.75/0.58    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(resolution,[],[f829,f107])).
% 1.75/0.58  fof(f829,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f814,f770])).
% 1.75/0.58  fof(f1037,plain,(
% 1.75/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19 | ~spl3_33)),
% 1.75/0.58    inference(backward_demodulation,[],[f934,f997])).
% 1.75/0.58  fof(f997,plain,(
% 1.75/0.58    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_33),
% 1.75/0.58    inference(avatar_component_clause,[],[f995])).
% 1.75/0.58  fof(f995,plain,(
% 1.75/0.58    spl3_33 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.75/0.58  fof(f934,plain,(
% 1.75/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(backward_demodulation,[],[f896,f880])).
% 1.75/0.58  fof(f880,plain,(
% 1.75/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f879,f58])).
% 1.75/0.58  fof(f879,plain,(
% 1.75/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f878,f821])).
% 1.75/0.58  fof(f878,plain,(
% 1.75/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f877,f829])).
% 1.75/0.58  fof(f877,plain,(
% 1.75/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f876,f62])).
% 1.75/0.58  fof(f876,plain,(
% 1.75/0.58    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(trivial_inequality_removal,[],[f869])).
% 1.75/0.58  fof(f869,plain,(
% 1.75/0.58    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(superposition,[],[f92,f863])).
% 1.75/0.58  fof(f863,plain,(
% 1.75/0.58    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f813,f770])).
% 1.75/0.58  fof(f896,plain,(
% 1.75/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f895,f770])).
% 1.75/0.58  fof(f1015,plain,(
% 1.75/0.58    ~spl3_1 | spl3_32),
% 1.75/0.58    inference(avatar_contradiction_clause,[],[f1014])).
% 1.75/0.58  fof(f1014,plain,(
% 1.75/0.58    $false | (~spl3_1 | spl3_32)),
% 1.75/0.58    inference(subsumption_resolution,[],[f1013,f118])).
% 1.75/0.58  fof(f1013,plain,(
% 1.75/0.58    ~v1_relat_1(sK2) | spl3_32),
% 1.75/0.58    inference(subsumption_resolution,[],[f1012,f58])).
% 1.75/0.58  fof(f1012,plain,(
% 1.75/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_32),
% 1.75/0.58    inference(subsumption_resolution,[],[f1011,f62])).
% 1.75/0.58  fof(f1011,plain,(
% 1.75/0.58    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_32),
% 1.75/0.58    inference(resolution,[],[f993,f68])).
% 1.75/0.58  fof(f68,plain,(
% 1.75/0.58    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f26])).
% 1.75/0.58  fof(f26,plain,(
% 1.75/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(flattening,[],[f25])).
% 1.75/0.58  fof(f25,plain,(
% 1.75/0.58    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.58    inference(ennf_transformation,[],[f3])).
% 1.75/0.58  fof(f3,axiom,(
% 1.75/0.58    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 1.75/0.58  fof(f993,plain,(
% 1.75/0.58    ~v2_funct_1(k2_funct_1(sK2)) | spl3_32),
% 1.75/0.58    inference(avatar_component_clause,[],[f991])).
% 1.75/0.58  fof(f991,plain,(
% 1.75/0.58    spl3_32 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.75/0.58  fof(f998,plain,(
% 1.75/0.58    ~spl3_32 | spl3_33 | ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_9 | ~spl3_19),
% 1.75/0.58    inference(avatar_split_clause,[],[f989,f379,f181,f145,f133,f127,f117,f995,f991])).
% 1.75/0.58  fof(f127,plain,(
% 1.75/0.58    spl3_3 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.75/0.58  fof(f133,plain,(
% 1.75/0.58    spl3_4 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.75/0.58  fof(f989,plain,(
% 1.75/0.58    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f988,f135])).
% 1.75/0.58  fof(f135,plain,(
% 1.75/0.58    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_4),
% 1.75/0.58    inference(avatar_component_clause,[],[f133])).
% 1.75/0.58  fof(f988,plain,(
% 1.75/0.58    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_6 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f987,f147])).
% 1.75/0.58  fof(f987,plain,(
% 1.75/0.58    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f986,f862])).
% 1.75/0.58  fof(f862,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f861,f380])).
% 1.75/0.58  fof(f861,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_9)),
% 1.75/0.58    inference(forward_demodulation,[],[f208,f770])).
% 1.75/0.58  fof(f208,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.75/0.58    inference(subsumption_resolution,[],[f207,f58])).
% 1.75/0.58  fof(f207,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(subsumption_resolution,[],[f206,f150])).
% 1.75/0.58  fof(f206,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(subsumption_resolution,[],[f205,f152])).
% 1.75/0.58  fof(f205,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(subsumption_resolution,[],[f198,f62])).
% 1.75/0.58  fof(f198,plain,(
% 1.75/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(trivial_inequality_removal,[],[f195])).
% 1.75/0.58  fof(f195,plain,(
% 1.75/0.58    k2_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(superposition,[],[f90,f192])).
% 1.75/0.58  fof(f90,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f42])).
% 1.75/0.58  fof(f986,plain,(
% 1.75/0.58    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f985,f888])).
% 1.75/0.58  fof(f888,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f887,f58])).
% 1.75/0.58  fof(f887,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f886,f821])).
% 1.75/0.58  fof(f886,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f885,f829])).
% 1.75/0.58  fof(f885,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f873,f62])).
% 1.75/0.58  fof(f873,plain,(
% 1.75/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(trivial_inequality_removal,[],[f872])).
% 1.75/0.58  fof(f872,plain,(
% 1.75/0.58    k2_relat_1(sK2) != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(superposition,[],[f91,f863])).
% 1.75/0.58  fof(f985,plain,(
% 1.75/0.58    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(trivial_inequality_removal,[],[f978])).
% 1.75/0.58  fof(f978,plain,(
% 1.75/0.58    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(superposition,[],[f92,f946])).
% 1.75/0.58  fof(f946,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_3 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f937,f129])).
% 1.75/0.58  fof(f129,plain,(
% 1.75/0.58    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_3),
% 1.75/0.58    inference(avatar_component_clause,[],[f127])).
% 1.75/0.58  fof(f937,plain,(
% 1.75/0.58    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_9 | ~spl3_19)),
% 1.75/0.58    inference(resolution,[],[f888,f78])).
% 1.75/0.58  fof(f78,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f35])).
% 1.75/0.58  fof(f35,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f7])).
% 1.75/0.58  fof(f7,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.75/0.58  fof(f570,plain,(
% 1.75/0.58    ~spl3_8 | spl3_19),
% 1.75/0.58    inference(avatar_contradiction_clause,[],[f569])).
% 1.75/0.58  fof(f569,plain,(
% 1.75/0.58    $false | (~spl3_8 | spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f568,f170])).
% 1.75/0.58  fof(f568,plain,(
% 1.75/0.58    k1_xboole_0 != k2_struct_0(sK1) | (~spl3_8 | spl3_19)),
% 1.75/0.58    inference(forward_demodulation,[],[f381,f299])).
% 1.75/0.58  fof(f299,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_8),
% 1.75/0.58    inference(forward_demodulation,[],[f280,f213])).
% 1.75/0.58  fof(f213,plain,(
% 1.75/0.58    k1_xboole_0 = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_8),
% 1.75/0.58    inference(backward_demodulation,[],[f192,f170])).
% 1.75/0.58  fof(f280,plain,(
% 1.75/0.58    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2) | ~spl3_8),
% 1.75/0.58    inference(resolution,[],[f214,f78])).
% 1.75/0.58  fof(f214,plain,(
% 1.75/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.75/0.58    inference(backward_demodulation,[],[f152,f170])).
% 1.75/0.58  fof(f381,plain,(
% 1.75/0.58    k2_struct_0(sK1) != k2_relat_1(sK2) | spl3_19),
% 1.75/0.58    inference(avatar_component_clause,[],[f379])).
% 1.75/0.58  fof(f489,plain,(
% 1.75/0.58    spl3_9 | spl3_8),
% 1.75/0.58    inference(avatar_split_clause,[],[f488,f168,f181])).
% 1.75/0.58  fof(f488,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.75/0.58    inference(subsumption_resolution,[],[f487,f58])).
% 1.75/0.58  fof(f487,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(subsumption_resolution,[],[f476,f150])).
% 1.75/0.58  fof(f476,plain,(
% 1.75/0.58    k1_xboole_0 = k2_struct_0(sK1) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2)),
% 1.75/0.58    inference(resolution,[],[f152,f106])).
% 1.75/0.58  fof(f402,plain,(
% 1.75/0.58    ~spl3_1 | ~spl3_9 | spl3_19),
% 1.75/0.58    inference(avatar_contradiction_clause,[],[f401])).
% 1.75/0.58  fof(f401,plain,(
% 1.75/0.58    $false | (~spl3_1 | ~spl3_9 | spl3_19)),
% 1.75/0.58    inference(subsumption_resolution,[],[f381,f365])).
% 1.75/0.58  fof(f365,plain,(
% 1.75/0.58    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_1 | ~spl3_9)),
% 1.75/0.58    inference(backward_demodulation,[],[f341,f321])).
% 1.75/0.58  fof(f321,plain,(
% 1.75/0.58    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_9)),
% 1.75/0.59    inference(resolution,[],[f317,f78])).
% 1.75/0.59  fof(f317,plain,(
% 1.75/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl3_1 | ~spl3_9)),
% 1.75/0.59    inference(forward_demodulation,[],[f152,f310])).
% 1.75/0.59  fof(f310,plain,(
% 1.75/0.59    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_1 | ~spl3_9)),
% 1.75/0.59    inference(subsumption_resolution,[],[f309,f118])).
% 1.75/0.59  fof(f309,plain,(
% 1.75/0.59    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_9),
% 1.75/0.59    inference(subsumption_resolution,[],[f308,f154])).
% 1.75/0.59  fof(f308,plain,(
% 1.75/0.59    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_9),
% 1.75/0.59    inference(resolution,[],[f183,f76])).
% 1.75/0.59  fof(f341,plain,(
% 1.75/0.59    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | (~spl3_1 | ~spl3_9)),
% 1.75/0.59    inference(forward_demodulation,[],[f192,f310])).
% 1.75/0.59  fof(f298,plain,(
% 1.75/0.59    spl3_16 | spl3_17 | ~spl3_8),
% 1.75/0.59    inference(avatar_split_clause,[],[f289,f168,f295,f291])).
% 1.75/0.59  fof(f289,plain,(
% 1.75/0.59    k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_8),
% 1.75/0.59    inference(subsumption_resolution,[],[f279,f215])).
% 1.75/0.59  fof(f215,plain,(
% 1.75/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~spl3_8),
% 1.75/0.59    inference(backward_demodulation,[],[f150,f170])).
% 1.75/0.59  fof(f279,plain,(
% 1.75/0.59    ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl3_8),
% 1.75/0.59    inference(resolution,[],[f214,f100])).
% 1.75/0.59  fof(f262,plain,(
% 1.75/0.59    ~spl3_12 | spl3_14 | ~spl3_8),
% 1.75/0.59    inference(avatar_split_clause,[],[f257,f168,f259,f247])).
% 1.75/0.59  fof(f257,plain,(
% 1.75/0.59    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~spl3_8),
% 1.75/0.59    inference(subsumption_resolution,[],[f256,f58])).
% 1.75/0.59  fof(f256,plain,(
% 1.75/0.59    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.75/0.59    inference(subsumption_resolution,[],[f255,f215])).
% 1.75/0.60  fof(f255,plain,(
% 1.75/0.60    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.75/0.60    inference(subsumption_resolution,[],[f240,f62])).
% 1.75/0.60  fof(f240,plain,(
% 1.75/0.60    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.75/0.60    inference(trivial_inequality_removal,[],[f237])).
% 1.75/0.60  fof(f237,plain,(
% 1.75/0.60    k1_xboole_0 != k1_xboole_0 | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_8),
% 1.75/0.60    inference(superposition,[],[f90,f213])).
% 1.75/0.60  fof(f189,plain,(
% 1.75/0.60    spl3_1),
% 1.75/0.60    inference(avatar_contradiction_clause,[],[f188])).
% 1.75/0.60  fof(f188,plain,(
% 1.75/0.60    $false | spl3_1),
% 1.75/0.60    inference(subsumption_resolution,[],[f187,f75])).
% 1.75/0.60  fof(f75,plain,(
% 1.75/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.75/0.60    inference(cnf_transformation,[],[f2])).
% 1.75/0.60  fof(f2,axiom,(
% 1.75/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.75/0.60  fof(f187,plain,(
% 1.75/0.60    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_1),
% 1.75/0.60    inference(subsumption_resolution,[],[f161,f119])).
% 1.75/0.60  fof(f119,plain,(
% 1.75/0.60    ~v1_relat_1(sK2) | spl3_1),
% 1.75/0.60    inference(avatar_component_clause,[],[f117])).
% 1.75/0.60  fof(f161,plain,(
% 1.75/0.60    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 1.75/0.60    inference(resolution,[],[f152,f65])).
% 1.75/0.60  fof(f65,plain,(
% 1.75/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f24])).
% 1.75/0.60  fof(f24,plain,(
% 1.75/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.75/0.60    inference(ennf_transformation,[],[f1])).
% 1.75/0.60  fof(f1,axiom,(
% 1.75/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.75/0.60  fof(f148,plain,(
% 1.75/0.60    ~spl3_1 | spl3_6),
% 1.75/0.60    inference(avatar_split_clause,[],[f143,f145,f117])).
% 1.75/0.60  fof(f143,plain,(
% 1.75/0.60    v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.75/0.60    inference(subsumption_resolution,[],[f114,f58])).
% 1.75/0.60  fof(f114,plain,(
% 1.75/0.60    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.75/0.60    inference(resolution,[],[f62,f67])).
% 1.75/0.60  fof(f67,plain,(
% 1.75/0.60    ( ! [X0] : (~v2_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f26])).
% 1.75/0.60  fof(f136,plain,(
% 1.75/0.60    ~spl3_1 | spl3_4),
% 1.75/0.60    inference(avatar_split_clause,[],[f131,f133,f117])).
% 1.75/0.60  fof(f131,plain,(
% 1.75/0.60    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.75/0.60    inference(subsumption_resolution,[],[f112,f58])).
% 1.75/0.60  fof(f112,plain,(
% 1.75/0.60    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.75/0.60    inference(resolution,[],[f62,f72])).
% 1.75/0.60  fof(f72,plain,(
% 1.75/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f30])).
% 1.75/0.60  fof(f30,plain,(
% 1.75/0.60    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.60    inference(flattening,[],[f29])).
% 1.75/0.60  fof(f29,plain,(
% 1.75/0.60    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.60    inference(ennf_transformation,[],[f5])).
% 1.75/0.60  fof(f5,axiom,(
% 1.75/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.75/0.60  fof(f130,plain,(
% 1.75/0.60    ~spl3_1 | spl3_3),
% 1.75/0.60    inference(avatar_split_clause,[],[f125,f127,f117])).
% 1.75/0.60  fof(f125,plain,(
% 1.75/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.75/0.60    inference(subsumption_resolution,[],[f111,f58])).
% 1.75/0.60  fof(f111,plain,(
% 1.75/0.60    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.75/0.60    inference(resolution,[],[f62,f74])).
% 1.75/0.60  fof(f74,plain,(
% 1.75/0.60    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.60    inference(cnf_transformation,[],[f32])).
% 1.75/0.60  fof(f32,plain,(
% 1.75/0.60    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.60    inference(flattening,[],[f31])).
% 1.75/0.60  fof(f31,plain,(
% 1.75/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.60    inference(ennf_transformation,[],[f4])).
% 1.75/0.60  fof(f4,axiom,(
% 1.75/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.75/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.75/0.60  % SZS output end Proof for theBenchmark
% 1.75/0.60  % (18850)------------------------------
% 1.75/0.60  % (18850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (18850)Termination reason: Refutation
% 1.75/0.60  
% 1.75/0.60  % (18850)Memory used [KB]: 11257
% 1.75/0.60  % (18850)Time elapsed: 0.164 s
% 1.75/0.60  % (18850)------------------------------
% 1.75/0.60  % (18850)------------------------------
% 1.92/0.60  % (18842)Success in time 0.249 s
%------------------------------------------------------------------------------
