%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  253 (2206 expanded)
%              Number of leaves         :   51 ( 829 expanded)
%              Depth                    :   17
%              Number of atoms          :  912 (15288 expanded)
%              Number of equality atoms :  158 (2310 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f385,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f121,f136,f139,f141,f165,f167,f175,f177,f202,f204,f214,f217,f226,f248,f261,f263,f271,f277,f284,f291,f297,f305,f314,f324,f326,f346,f375,f382,f384])).

fof(f384,plain,
    ( ~ spl3_15
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl3_15
    | spl3_31 ),
    inference(resolution,[],[f381,f230])).

fof(f230,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f185,f213])).

fof(f213,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f211])).

fof(f211,plain,
    ( spl3_15
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f185,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f107,f181])).

fof(f181,plain,(
    k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f106,f180])).

fof(f180,plain,(
    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f79,f107])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f106,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f103,f100])).

fof(f100,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f67,f56])).

fof(f56,plain,(
    l1_struct_0(sK1) ),
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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f103,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f60,f99])).

fof(f99,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f67,f54])).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f60,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f102,f100])).

fof(f102,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f59,f99])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f381,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl3_31
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f382,plain,
    ( ~ spl3_4
    | ~ spl3_18
    | ~ spl3_31
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f377,f372,f302,f211,f379,f254,f129])).

fof(f129,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f254,plain,
    ( spl3_18
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f302,plain,
    ( spl3_24
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f372,plain,
    ( spl3_30
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f377,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(resolution,[],[f376,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(condensation,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f376,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_15
    | ~ spl3_24
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f306,f374])).

fof(f374,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f372])).

fof(f306,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f231,f304])).

fof(f304,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f302])).

fof(f231,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f186,f213])).

fof(f186,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    inference(backward_demodulation,[],[f105,f181])).

fof(f105,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f104,f100])).

fof(f104,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f62,f99])).

fof(f62,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f375,plain,
    ( spl3_30
    | ~ spl3_19
    | ~ spl3_9
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f370,f344,f268,f159,f258,f372])).

fof(f258,plain,
    ( spl3_19
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f159,plain,
    ( spl3_9
  <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f268,plain,
    ( spl3_20
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f344,plain,
    ( spl3_28
  <=> ! [X3,X2] :
        ( sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f370,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(trivial_inequality_removal,[],[f369])).

fof(f369,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f368,f278])).

fof(f278,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_9
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f276,f161])).

fof(f161,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f276,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(resolution,[],[f270,f79])).

fof(f270,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f268])).

fof(f368,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_20
    | ~ spl3_28 ),
    inference(resolution,[],[f345,f270])).

fof(f345,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f344])).

fof(f346,plain,
    ( ~ spl3_7
    | spl3_28
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f342,f155,f133,f344,f151])).

fof(f151,plain,
    ( spl3_7
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f133,plain,
    ( spl3_5
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f155,plain,
    ( spl3_8
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f342,plain,
    ( ! [X2,X3] :
        ( sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_5
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f334,f135])).

fof(f135,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f133])).

fof(f334,plain,
    ( ! [X2,X3] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_8 ),
    inference(resolution,[],[f156,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f156,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f326,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | spl3_26 ),
    inference(resolution,[],[f323,f91])).

fof(f91,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f66,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f66,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f323,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl3_26
  <=> v2_funct_1(k6_partfun1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f324,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | ~ spl3_3
    | ~ spl3_4
    | spl3_8
    | ~ spl3_26
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f319,f311,f281,f321,f155,f129,f125,f151,f147])).

fof(f147,plain,
    ( spl3_6
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f125,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f281,plain,
    ( spl3_21
  <=> k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f311,plain,
    ( spl3_25
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f319,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f318])).

fof(f318,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f316,f283])).

fof(f283,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f281])).

fof(f316,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_25 ),
    inference(superposition,[],[f75,f313])).

fof(f313,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f311])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f314,plain,
    ( spl3_25
    | spl3_13
    | ~ spl3_18
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f309,f295,f211,f254,f199,f311])).

fof(f199,plain,
    ( spl3_13
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f295,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0
        | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f309,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f307,f228])).

fof(f228,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f182,f213])).

fof(f182,plain,(
    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f180,f181])).

fof(f307,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(resolution,[],[f296,f230])).

fof(f296,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k1_xboole_0 = X0
        | k2_relset_1(X1,X0,sK2) != X0
        | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f295])).

fof(f305,plain,
    ( spl3_24
    | ~ spl3_18
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f300,f289,f211,f254,f302])).

fof(f289,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f300,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f298,f228])).

fof(f298,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_15
    | ~ spl3_22 ),
    inference(resolution,[],[f290,f230])).

fof(f290,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f289])).

fof(f297,plain,
    ( ~ spl3_4
    | spl3_23 ),
    inference(avatar_split_clause,[],[f292,f295,f129])).

fof(f292,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X1,X0,sK2) != X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK2,X1,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f86,f61])).

fof(f61,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
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
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f291,plain,
    ( ~ spl3_4
    | spl3_22 ),
    inference(avatar_split_clause,[],[f286,f289,f129])).

fof(f286,plain,(
    ! [X0,X1] :
      ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f85,f61])).

fof(f284,plain,
    ( ~ spl3_6
    | ~ spl3_17
    | spl3_21
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f279,f241,f281,f245,f147])).

fof(f245,plain,
    ( spl3_17
  <=> v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f241,plain,
    ( spl3_16
  <=> v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f279,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | ~ v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_16 ),
    inference(resolution,[],[f243,f76])).

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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f243,plain,
    ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f241])).

fof(f277,plain,
    ( spl3_17
    | ~ spl3_20 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | spl3_17
    | ~ spl3_20 ),
    inference(resolution,[],[f270,f249])).

fof(f249,plain,
    ( ! [X0] : ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0)))
    | spl3_17 ),
    inference(resolution,[],[f247,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f247,plain,
    ( ~ v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f245])).

fof(f271,plain,
    ( ~ spl3_4
    | ~ spl3_18
    | spl3_20
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f266,f211,f172,f268,f254,f129])).

fof(f172,plain,
    ( spl3_10
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f266,plain,
    ( ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(trivial_inequality_removal,[],[f265])).

fof(f265,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f264,f228])).

fof(f264,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f84,f230])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f263,plain,
    ( ~ spl3_15
    | spl3_18 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_15
    | spl3_18 ),
    inference(resolution,[],[f256,f229])).

fof(f229,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f184,f213])).

fof(f184,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f108,f181])).

fof(f108,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f101,f100])).

fof(f101,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f58,f99])).

fof(f58,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f256,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f254])).

fof(f261,plain,
    ( ~ spl3_4
    | ~ spl3_18
    | spl3_19
    | ~ spl3_10
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f252,f211,f172,f258,f254,f129])).

fof(f252,plain,
    ( ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(trivial_inequality_removal,[],[f251])).

fof(f251,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f250,f228])).

fof(f250,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f83,f230])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f248,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_16
    | ~ spl3_6
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f238,f245,f147,f241,f129,f125])).

fof(f238,plain,
    ( ~ v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f142,f61])).

fof(f142,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v4_relat_1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | v1_partfun1(k2_funct_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f93,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f93,plain,(
    ! [X1] :
      ( v1_partfun1(X1,k1_relat_1(X1))
      | ~ v4_relat_1(X1,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_partfun1(X1,X0)
      | k1_relat_1(X1) != X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f226,plain,
    ( spl3_2
    | ~ spl3_13 ),
    inference(avatar_contradiction_clause,[],[f225])).

fof(f225,plain,
    ( $false
    | spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f220,f63])).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f220,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_2
    | ~ spl3_13 ),
    inference(backward_demodulation,[],[f183,f201])).

fof(f201,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f199])).

fof(f183,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_2 ),
    inference(backward_demodulation,[],[f118,f181])).

fof(f118,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_2
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f217,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f215,f185])).

fof(f215,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl3_14 ),
    inference(resolution,[],[f209,f80])).

fof(f209,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl3_14
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f214,plain,
    ( ~ spl3_3
    | ~ spl3_14
    | spl3_15
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f205,f195,f211,f207,f125])).

fof(f195,plain,
    ( spl3_12
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f205,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_12 ),
    inference(resolution,[],[f197,f76])).

fof(f197,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f195])).

fof(f204,plain,(
    spl3_11 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl3_11 ),
    inference(resolution,[],[f193,f184])).

fof(f193,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl3_11
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f202,plain,
    ( ~ spl3_4
    | ~ spl3_11
    | spl3_12
    | spl3_13 ),
    inference(avatar_split_clause,[],[f189,f199,f195,f191,f129])).

fof(f189,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f97,f185])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f177,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f174,f61])).

fof(f174,plain,
    ( ~ v2_funct_1(sK2)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f172])).

fof(f175,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | spl3_9 ),
    inference(avatar_split_clause,[],[f170,f159,f172,f129,f125])).

fof(f170,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(trivial_inequality_removal,[],[f169])).

fof(f169,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_9 ),
    inference(superposition,[],[f160,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f160,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f159])).

fof(f167,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f166,f151,f129,f125])).

fof(f166,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f153,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f153,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f151])).

fof(f165,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f163,f147,f129,f125])).

fof(f163,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_6 ),
    inference(resolution,[],[f149,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f141,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f137,f107])).

fof(f137,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_3 ),
    inference(resolution,[],[f127,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f139,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f138])).

fof(f138,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f131,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f131,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f136,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f122,f133,f129,f125])).

fof(f122,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f71,f61])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f121,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f114,f56])).

fof(f114,plain,
    ( ~ l1_struct_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl3_1
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f119,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f110,f116,f112])).

fof(f110,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f109,f100])).

fof(f109,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f68,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f68,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:08:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (14682)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (14680)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (14684)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (14688)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  % (14690)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.56  % (14692)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.56  % (14676)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (14672)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (14674)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (14674)Refutation not found, incomplete strategy% (14674)------------------------------
% 0.22/0.56  % (14674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (14676)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % (14674)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (14674)Memory used [KB]: 10746
% 0.22/0.57  % (14674)Time elapsed: 0.117 s
% 0.22/0.57  % (14674)------------------------------
% 0.22/0.57  % (14674)------------------------------
% 0.22/0.58  % SZS output start Proof for theBenchmark
% 0.22/0.58  fof(f385,plain,(
% 0.22/0.58    $false),
% 0.22/0.58    inference(avatar_sat_refutation,[],[f119,f121,f136,f139,f141,f165,f167,f175,f177,f202,f204,f214,f217,f226,f248,f261,f263,f271,f277,f284,f291,f297,f305,f314,f324,f326,f346,f375,f382,f384])).
% 0.22/0.58  fof(f384,plain,(
% 0.22/0.58    ~spl3_15 | spl3_31),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f383])).
% 0.22/0.58  fof(f383,plain,(
% 0.22/0.58    $false | (~spl3_15 | spl3_31)),
% 0.22/0.58    inference(resolution,[],[f381,f230])).
% 0.22/0.58  fof(f230,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_15),
% 0.22/0.58    inference(backward_demodulation,[],[f185,f213])).
% 0.22/0.58  fof(f213,plain,(
% 0.22/0.58    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_15),
% 0.22/0.58    inference(avatar_component_clause,[],[f211])).
% 0.22/0.58  fof(f211,plain,(
% 0.22/0.58    spl3_15 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.58  fof(f185,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.22/0.58    inference(backward_demodulation,[],[f107,f181])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f106,f180])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.22/0.58    inference(resolution,[],[f79,f107])).
% 0.22/0.58  fof(f79,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f9])).
% 0.22/0.58  fof(f9,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.58  fof(f106,plain,(
% 0.22/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f103,f100])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.58    inference(resolution,[],[f67,f56])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    l1_struct_0(sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f52])).
% 0.22/0.58  fof(f52,plain,(
% 0.22/0.58    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).
% 0.22/0.58  fof(f49,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f50,plain,(
% 0.22/0.58    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f51,plain,(
% 0.22/0.58    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,negated_conjecture,(
% 0.22/0.58    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.58    inference(negated_conjecture,[],[f19])).
% 0.22/0.58  fof(f19,conjecture,(
% 0.22/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tops_2)).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.58    inference(ennf_transformation,[],[f16])).
% 0.22/0.58  fof(f16,axiom,(
% 0.22/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.58  fof(f103,plain,(
% 0.22/0.58    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f60,f99])).
% 0.22/0.58  fof(f99,plain,(
% 0.22/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.58    inference(resolution,[],[f67,f54])).
% 0.22/0.58  fof(f54,plain,(
% 0.22/0.58    l1_struct_0(sK0)),
% 0.22/0.58    inference(cnf_transformation,[],[f52])).
% 0.22/0.58  fof(f60,plain,(
% 0.22/0.58    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f52])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.58    inference(backward_demodulation,[],[f102,f100])).
% 0.22/0.58  fof(f102,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.58    inference(backward_demodulation,[],[f59,f99])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.58    inference(cnf_transformation,[],[f52])).
% 0.22/0.58  fof(f381,plain,(
% 0.22/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | spl3_31),
% 0.22/0.58    inference(avatar_component_clause,[],[f379])).
% 0.22/0.58  fof(f379,plain,(
% 0.22/0.58    spl3_31 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.22/0.58  fof(f382,plain,(
% 0.22/0.58    ~spl3_4 | ~spl3_18 | ~spl3_31 | ~spl3_15 | ~spl3_24 | ~spl3_30),
% 0.22/0.58    inference(avatar_split_clause,[],[f377,f372,f302,f211,f379,f254,f129])).
% 0.22/0.58  fof(f129,plain,(
% 0.22/0.58    spl3_4 <=> v1_funct_1(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.58  fof(f254,plain,(
% 0.22/0.58    spl3_18 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.58  fof(f302,plain,(
% 0.22/0.58    spl3_24 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.58  fof(f372,plain,(
% 0.22/0.58    spl3_30 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.22/0.58  fof(f377,plain,(
% 0.22/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_15 | ~spl3_24 | ~spl3_30)),
% 0.22/0.58    inference(resolution,[],[f376,f96])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (r2_funct_2(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f95])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 0.22/0.58    inference(condensation,[],[f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f48])).
% 0.22/0.58  fof(f48,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.58    inference(flattening,[],[f47])).
% 0.22/0.58  fof(f47,plain,(
% 0.22/0.58    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.22/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.22/0.58  fof(f376,plain,(
% 0.22/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_15 | ~spl3_24 | ~spl3_30)),
% 0.22/0.58    inference(backward_demodulation,[],[f306,f374])).
% 0.22/0.58  fof(f374,plain,(
% 0.22/0.58    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_30),
% 0.22/0.58    inference(avatar_component_clause,[],[f372])).
% 0.22/0.58  fof(f306,plain,(
% 0.22/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (~spl3_15 | ~spl3_24)),
% 0.22/0.58    inference(backward_demodulation,[],[f231,f304])).
% 0.22/0.58  fof(f304,plain,(
% 0.22/0.58    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_24),
% 0.22/0.58    inference(avatar_component_clause,[],[f302])).
% 0.22/0.58  fof(f231,plain,(
% 0.22/0.58    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | ~spl3_15),
% 0.22/0.58    inference(backward_demodulation,[],[f186,f213])).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f105,f181])).
% 0.22/0.58  fof(f105,plain,(
% 0.22/0.58    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f104,f100])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.22/0.58    inference(backward_demodulation,[],[f62,f99])).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f52])).
% 0.22/0.58  fof(f375,plain,(
% 0.22/0.58    spl3_30 | ~spl3_19 | ~spl3_9 | ~spl3_20 | ~spl3_28),
% 0.22/0.58    inference(avatar_split_clause,[],[f370,f344,f268,f159,f258,f372])).
% 0.22/0.58  fof(f258,plain,(
% 0.22/0.58    spl3_19 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    spl3_9 <=> k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.58  fof(f268,plain,(
% 0.22/0.58    spl3_20 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.58  fof(f344,plain,(
% 0.22/0.58    spl3_28 <=> ! [X3,X2] : (sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.58  fof(f370,plain,(
% 0.22/0.58    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_9 | ~spl3_20 | ~spl3_28)),
% 0.22/0.58    inference(trivial_inequality_removal,[],[f369])).
% 0.22/0.58  fof(f369,plain,(
% 0.22/0.58    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_9 | ~spl3_20 | ~spl3_28)),
% 0.22/0.58    inference(forward_demodulation,[],[f368,f278])).
% 0.22/0.58  fof(f278,plain,(
% 0.22/0.58    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_9 | ~spl3_20)),
% 0.22/0.58    inference(forward_demodulation,[],[f276,f161])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) | ~spl3_9),
% 0.22/0.58    inference(avatar_component_clause,[],[f159])).
% 0.22/0.58  fof(f276,plain,(
% 0.22/0.58    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_20),
% 0.22/0.58    inference(resolution,[],[f270,f79])).
% 0.22/0.58  fof(f270,plain,(
% 0.22/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_20),
% 0.22/0.58    inference(avatar_component_clause,[],[f268])).
% 0.22/0.58  fof(f368,plain,(
% 0.22/0.58    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_20 | ~spl3_28)),
% 0.22/0.58    inference(resolution,[],[f345,f270])).
% 0.22/0.58  fof(f345,plain,(
% 0.22/0.58    ( ! [X2,X3] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2)) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3) ) | ~spl3_28),
% 0.22/0.58    inference(avatar_component_clause,[],[f344])).
% 0.22/0.58  fof(f346,plain,(
% 0.22/0.58    ~spl3_7 | spl3_28 | ~spl3_5 | ~spl3_8),
% 0.22/0.58    inference(avatar_split_clause,[],[f342,f155,f133,f344,f151])).
% 0.22/0.58  fof(f151,plain,(
% 0.22/0.58    spl3_7 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.58  fof(f133,plain,(
% 0.22/0.58    spl3_5 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.58  fof(f155,plain,(
% 0.22/0.58    spl3_8 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.58  fof(f342,plain,(
% 0.22/0.58    ( ! [X2,X3] : (sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2)) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~v1_funct_1(k2_funct_1(sK2))) ) | (~spl3_5 | ~spl3_8)),
% 0.22/0.58    inference(forward_demodulation,[],[f334,f135])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_5),
% 0.22/0.58    inference(avatar_component_clause,[],[f133])).
% 0.22/0.58  fof(f334,plain,(
% 0.22/0.58    ( ! [X2,X3] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl3_8),
% 0.22/0.58    inference(resolution,[],[f156,f85])).
% 0.22/0.58  fof(f85,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f42])).
% 0.22/0.59  fof(f42,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f41])).
% 0.22/0.59  fof(f41,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.59  fof(f156,plain,(
% 0.22/0.59    v2_funct_1(k2_funct_1(sK2)) | ~spl3_8),
% 0.22/0.59    inference(avatar_component_clause,[],[f155])).
% 0.22/0.59  fof(f326,plain,(
% 0.22/0.59    spl3_26),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f325])).
% 0.22/0.59  fof(f325,plain,(
% 0.22/0.59    $false | spl3_26),
% 0.22/0.59    inference(resolution,[],[f323,f91])).
% 0.22/0.59  fof(f91,plain,(
% 0.22/0.59    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.22/0.59    inference(definition_unfolding,[],[f66,f64])).
% 0.22/0.59  fof(f64,plain,(
% 0.22/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f11])).
% 0.22/0.59  fof(f11,axiom,(
% 0.22/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f3])).
% 0.22/0.59  fof(f3,axiom,(
% 0.22/0.59    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.59  fof(f323,plain,(
% 0.22/0.59    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | spl3_26),
% 0.22/0.59    inference(avatar_component_clause,[],[f321])).
% 0.22/0.59  fof(f321,plain,(
% 0.22/0.59    spl3_26 <=> v2_funct_1(k6_partfun1(k1_relat_1(sK2)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.22/0.59  fof(f324,plain,(
% 0.22/0.59    ~spl3_6 | ~spl3_7 | ~spl3_3 | ~spl3_4 | spl3_8 | ~spl3_26 | ~spl3_21 | ~spl3_25),
% 0.22/0.59    inference(avatar_split_clause,[],[f319,f311,f281,f321,f155,f129,f125,f151,f147])).
% 0.22/0.59  fof(f147,plain,(
% 0.22/0.59    spl3_6 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.59  fof(f125,plain,(
% 0.22/0.59    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.59  fof(f281,plain,(
% 0.22/0.59    spl3_21 <=> k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.59  fof(f311,plain,(
% 0.22/0.59    spl3_25 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.59  fof(f319,plain,(
% 0.22/0.59    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_21 | ~spl3_25)),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f318])).
% 0.22/0.59  fof(f318,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_21 | ~spl3_25)),
% 0.22/0.59    inference(forward_demodulation,[],[f316,f283])).
% 0.22/0.59  fof(f283,plain,(
% 0.22/0.59    k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) | ~spl3_21),
% 0.22/0.59    inference(avatar_component_clause,[],[f281])).
% 0.22/0.59  fof(f316,plain,(
% 0.22/0.59    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_25),
% 0.22/0.59    inference(superposition,[],[f75,f313])).
% 0.22/0.59  fof(f313,plain,(
% 0.22/0.59    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | ~spl3_25),
% 0.22/0.59    inference(avatar_component_clause,[],[f311])).
% 0.22/0.59  fof(f75,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f33])).
% 0.22/0.59  fof(f33,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f32])).
% 0.22/0.59  fof(f32,plain,(
% 0.22/0.59    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.59    inference(ennf_transformation,[],[f4])).
% 0.22/0.59  fof(f4,axiom,(
% 0.22/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 0.22/0.59  fof(f314,plain,(
% 0.22/0.59    spl3_25 | spl3_13 | ~spl3_18 | ~spl3_15 | ~spl3_23),
% 0.22/0.59    inference(avatar_split_clause,[],[f309,f295,f211,f254,f199,f311])).
% 0.22/0.59  fof(f199,plain,(
% 0.22/0.59    spl3_13 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.22/0.59  fof(f295,plain,(
% 0.22/0.59    spl3_23 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.59  fof(f309,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | (~spl3_15 | ~spl3_23)),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f308])).
% 0.22/0.59  fof(f308,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | (~spl3_15 | ~spl3_23)),
% 0.22/0.59    inference(forward_demodulation,[],[f307,f228])).
% 0.22/0.59  fof(f228,plain,(
% 0.22/0.59    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_15),
% 0.22/0.59    inference(backward_demodulation,[],[f182,f213])).
% 0.22/0.59  fof(f182,plain,(
% 0.22/0.59    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.22/0.59    inference(backward_demodulation,[],[f180,f181])).
% 0.22/0.59  fof(f307,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) | (~spl3_15 | ~spl3_23)),
% 0.22/0.59    inference(resolution,[],[f296,f230])).
% 0.22/0.59  fof(f296,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k1_xboole_0 = X0 | k2_relset_1(X1,X0,sK2) != X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))) ) | ~spl3_23),
% 0.22/0.59    inference(avatar_component_clause,[],[f295])).
% 0.22/0.59  fof(f305,plain,(
% 0.22/0.59    spl3_24 | ~spl3_18 | ~spl3_15 | ~spl3_22),
% 0.22/0.59    inference(avatar_split_clause,[],[f300,f289,f211,f254,f302])).
% 0.22/0.59  fof(f289,plain,(
% 0.22/0.59    spl3_22 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.59  fof(f300,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_15 | ~spl3_22)),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f299])).
% 0.22/0.59  fof(f299,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_15 | ~spl3_22)),
% 0.22/0.59    inference(forward_demodulation,[],[f298,f228])).
% 0.22/0.59  fof(f298,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_15 | ~spl3_22)),
% 0.22/0.59    inference(resolution,[],[f290,f230])).
% 0.22/0.59  fof(f290,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_22),
% 0.22/0.59    inference(avatar_component_clause,[],[f289])).
% 0.22/0.59  fof(f297,plain,(
% 0.22/0.59    ~spl3_4 | spl3_23),
% 0.22/0.59    inference(avatar_split_clause,[],[f292,f295,f129])).
% 0.22/0.59  fof(f292,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~v1_funct_1(sK2)) )),
% 0.22/0.59    inference(resolution,[],[f86,f61])).
% 0.22/0.59  fof(f61,plain,(
% 0.22/0.59    v2_funct_1(sK2)),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f86,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f44])).
% 0.22/0.59  fof(f44,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f43])).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f15])).
% 0.22/0.59  fof(f15,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.59  fof(f291,plain,(
% 0.22/0.59    ~spl3_4 | spl3_22),
% 0.22/0.59    inference(avatar_split_clause,[],[f286,f289,f129])).
% 0.22/0.59  fof(f286,plain,(
% 0.22/0.59    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 0.22/0.59    inference(resolution,[],[f85,f61])).
% 0.22/0.59  fof(f284,plain,(
% 0.22/0.59    ~spl3_6 | ~spl3_17 | spl3_21 | ~spl3_16),
% 0.22/0.59    inference(avatar_split_clause,[],[f279,f241,f281,f245,f147])).
% 0.22/0.59  fof(f245,plain,(
% 0.22/0.59    spl3_17 <=> v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.59  fof(f241,plain,(
% 0.22/0.59    spl3_16 <=> v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2))),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.59  fof(f279,plain,(
% 0.22/0.59    k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) | ~v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_16),
% 0.22/0.59    inference(resolution,[],[f243,f76])).
% 0.22/0.59  fof(f76,plain,(
% 0.22/0.59    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f53])).
% 0.22/0.59  fof(f53,plain,(
% 0.22/0.59    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(nnf_transformation,[],[f35])).
% 0.22/0.59  fof(f35,plain,(
% 0.22/0.59    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.59    inference(flattening,[],[f34])).
% 0.22/0.59  fof(f34,plain,(
% 0.22/0.59    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.59    inference(ennf_transformation,[],[f10])).
% 0.22/0.59  fof(f10,axiom,(
% 0.22/0.59    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.59  fof(f243,plain,(
% 0.22/0.59    v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~spl3_16),
% 0.22/0.59    inference(avatar_component_clause,[],[f241])).
% 0.22/0.59  fof(f277,plain,(
% 0.22/0.59    spl3_17 | ~spl3_20),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f272])).
% 0.22/0.59  fof(f272,plain,(
% 0.22/0.59    $false | (spl3_17 | ~spl3_20)),
% 0.22/0.59    inference(resolution,[],[f270,f249])).
% 0.22/0.59  fof(f249,plain,(
% 0.22/0.59    ( ! [X0] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0)))) ) | spl3_17),
% 0.22/0.59    inference(resolution,[],[f247,f80])).
% 0.22/0.59  fof(f80,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f38])).
% 0.22/0.59  fof(f38,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.59    inference(ennf_transformation,[],[f8])).
% 0.22/0.59  fof(f8,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.59  fof(f247,plain,(
% 0.22/0.59    ~v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | spl3_17),
% 0.22/0.59    inference(avatar_component_clause,[],[f245])).
% 0.22/0.59  fof(f271,plain,(
% 0.22/0.59    ~spl3_4 | ~spl3_18 | spl3_20 | ~spl3_10 | ~spl3_15),
% 0.22/0.59    inference(avatar_split_clause,[],[f266,f211,f172,f268,f254,f129])).
% 0.22/0.59  fof(f172,plain,(
% 0.22/0.59    spl3_10 <=> v2_funct_1(sK2)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.59  fof(f266,plain,(
% 0.22/0.59    ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f265])).
% 0.22/0.59  fof(f265,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.59    inference(forward_demodulation,[],[f264,f228])).
% 0.22/0.59  fof(f264,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.59    inference(resolution,[],[f84,f230])).
% 0.22/0.59  fof(f84,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f40])).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.59    inference(flattening,[],[f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.59    inference(ennf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.22/0.59  fof(f263,plain,(
% 0.22/0.59    ~spl3_15 | spl3_18),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f262])).
% 0.22/0.59  fof(f262,plain,(
% 0.22/0.59    $false | (~spl3_15 | spl3_18)),
% 0.22/0.59    inference(resolution,[],[f256,f229])).
% 0.22/0.59  fof(f229,plain,(
% 0.22/0.59    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_15),
% 0.22/0.59    inference(backward_demodulation,[],[f184,f213])).
% 0.22/0.59  fof(f184,plain,(
% 0.22/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.59    inference(backward_demodulation,[],[f108,f181])).
% 0.22/0.59  fof(f108,plain,(
% 0.22/0.59    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f101,f100])).
% 0.22/0.59  fof(f101,plain,(
% 0.22/0.59    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.59    inference(backward_demodulation,[],[f58,f99])).
% 0.22/0.59  fof(f58,plain,(
% 0.22/0.59    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.59    inference(cnf_transformation,[],[f52])).
% 0.22/0.59  fof(f256,plain,(
% 0.22/0.59    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | spl3_18),
% 0.22/0.59    inference(avatar_component_clause,[],[f254])).
% 0.22/0.59  fof(f261,plain,(
% 0.22/0.59    ~spl3_4 | ~spl3_18 | spl3_19 | ~spl3_10 | ~spl3_15),
% 0.22/0.59    inference(avatar_split_clause,[],[f252,f211,f172,f258,f254,f129])).
% 0.22/0.59  fof(f252,plain,(
% 0.22/0.59    ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.59    inference(trivial_inequality_removal,[],[f251])).
% 0.22/0.59  fof(f251,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.59    inference(forward_demodulation,[],[f250,f228])).
% 0.22/0.59  fof(f250,plain,(
% 0.22/0.59    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_15),
% 0.22/0.59    inference(resolution,[],[f83,f230])).
% 0.22/0.59  fof(f83,plain,(
% 0.22/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f40])).
% 0.22/0.59  fof(f248,plain,(
% 0.22/0.59    ~spl3_3 | ~spl3_4 | spl3_16 | ~spl3_6 | ~spl3_17),
% 0.22/0.59    inference(avatar_split_clause,[],[f238,f245,f147,f241,f129,f125])).
% 0.22/0.59  fof(f238,plain,(
% 0.22/0.59    ~v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.59    inference(resolution,[],[f142,f61])).
% 0.22/0.59  fof(f142,plain,(
% 0.22/0.59    ( ! [X0] : (~v2_funct_1(X0) | ~v4_relat_1(k2_funct_1(X0),k2_relat_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | v1_partfun1(k2_funct_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(superposition,[],[f93,f72])).
% 0.22/0.59  fof(f72,plain,(
% 0.22/0.59    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f31])).
% 0.22/0.59  fof(f31,plain,(
% 0.22/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.59    inference(flattening,[],[f30])).
% 0.22/0.60  fof(f30,plain,(
% 0.22/0.60    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f5])).
% 0.22/0.60  fof(f5,axiom,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.22/0.60  fof(f93,plain,(
% 0.22/0.60    ( ! [X1] : (v1_partfun1(X1,k1_relat_1(X1)) | ~v4_relat_1(X1,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.60    inference(equality_resolution,[],[f77])).
% 0.22/0.60  fof(f77,plain,(
% 0.22/0.60    ( ! [X0,X1] : (v1_partfun1(X1,X0) | k1_relat_1(X1) != X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f53])).
% 0.22/0.60  fof(f226,plain,(
% 0.22/0.60    spl3_2 | ~spl3_13),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f225])).
% 0.22/0.60  fof(f225,plain,(
% 0.22/0.60    $false | (spl3_2 | ~spl3_13)),
% 0.22/0.60    inference(resolution,[],[f220,f63])).
% 0.22/0.60  fof(f63,plain,(
% 0.22/0.60    v1_xboole_0(k1_xboole_0)),
% 0.22/0.60    inference(cnf_transformation,[],[f1])).
% 0.22/0.60  fof(f1,axiom,(
% 0.22/0.60    v1_xboole_0(k1_xboole_0)),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.60  fof(f220,plain,(
% 0.22/0.60    ~v1_xboole_0(k1_xboole_0) | (spl3_2 | ~spl3_13)),
% 0.22/0.60    inference(backward_demodulation,[],[f183,f201])).
% 0.22/0.60  fof(f201,plain,(
% 0.22/0.60    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_13),
% 0.22/0.60    inference(avatar_component_clause,[],[f199])).
% 0.22/0.60  fof(f183,plain,(
% 0.22/0.60    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_2),
% 0.22/0.60    inference(backward_demodulation,[],[f118,f181])).
% 0.22/0.60  fof(f118,plain,(
% 0.22/0.60    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_2),
% 0.22/0.60    inference(avatar_component_clause,[],[f116])).
% 0.22/0.60  fof(f116,plain,(
% 0.22/0.60    spl3_2 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.60  fof(f217,plain,(
% 0.22/0.60    spl3_14),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f216])).
% 0.22/0.60  fof(f216,plain,(
% 0.22/0.60    $false | spl3_14),
% 0.22/0.60    inference(resolution,[],[f215,f185])).
% 0.22/0.60  fof(f215,plain,(
% 0.22/0.60    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | spl3_14),
% 0.22/0.60    inference(resolution,[],[f209,f80])).
% 0.22/0.60  fof(f209,plain,(
% 0.22/0.60    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_14),
% 0.22/0.60    inference(avatar_component_clause,[],[f207])).
% 0.22/0.60  fof(f207,plain,(
% 0.22/0.60    spl3_14 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.60  fof(f214,plain,(
% 0.22/0.60    ~spl3_3 | ~spl3_14 | spl3_15 | ~spl3_12),
% 0.22/0.60    inference(avatar_split_clause,[],[f205,f195,f211,f207,f125])).
% 0.22/0.60  fof(f195,plain,(
% 0.22/0.60    spl3_12 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.60  fof(f205,plain,(
% 0.22/0.60    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_12),
% 0.22/0.60    inference(resolution,[],[f197,f76])).
% 0.22/0.60  fof(f197,plain,(
% 0.22/0.60    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_12),
% 0.22/0.60    inference(avatar_component_clause,[],[f195])).
% 0.22/0.60  fof(f204,plain,(
% 0.22/0.60    spl3_11),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.60  fof(f203,plain,(
% 0.22/0.60    $false | spl3_11),
% 0.22/0.60    inference(resolution,[],[f193,f184])).
% 0.22/0.60  fof(f193,plain,(
% 0.22/0.60    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | spl3_11),
% 0.22/0.60    inference(avatar_component_clause,[],[f191])).
% 0.22/0.60  fof(f191,plain,(
% 0.22/0.60    spl3_11 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.60  fof(f202,plain,(
% 0.22/0.60    ~spl3_4 | ~spl3_11 | spl3_12 | spl3_13),
% 0.22/0.60    inference(avatar_split_clause,[],[f189,f199,f195,f191,f129])).
% 0.22/0.60  fof(f189,plain,(
% 0.22/0.60    k1_xboole_0 = k2_relat_1(sK2) | v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f97,f185])).
% 0.22/0.60  fof(f97,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.60    inference(duplicate_literal_removal,[],[f88])).
% 0.22/0.60  fof(f88,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f46])).
% 0.22/0.60  fof(f46,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.60    inference(flattening,[],[f45])).
% 0.22/0.60  fof(f45,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.60    inference(ennf_transformation,[],[f13])).
% 0.22/0.60  fof(f13,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.60  fof(f177,plain,(
% 0.22/0.60    spl3_10),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f176])).
% 0.22/0.60  fof(f176,plain,(
% 0.22/0.60    $false | spl3_10),
% 0.22/0.60    inference(resolution,[],[f174,f61])).
% 0.22/0.60  fof(f174,plain,(
% 0.22/0.60    ~v2_funct_1(sK2) | spl3_10),
% 0.22/0.60    inference(avatar_component_clause,[],[f172])).
% 0.22/0.60  fof(f175,plain,(
% 0.22/0.60    ~spl3_3 | ~spl3_4 | ~spl3_10 | spl3_9),
% 0.22/0.60    inference(avatar_split_clause,[],[f170,f159,f172,f129,f125])).
% 0.22/0.60  fof(f170,plain,(
% 0.22/0.60    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_9),
% 0.22/0.60    inference(trivial_inequality_removal,[],[f169])).
% 0.22/0.60  fof(f169,plain,(
% 0.22/0.60    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_9),
% 0.22/0.60    inference(superposition,[],[f160,f73])).
% 0.22/0.60  fof(f73,plain,(
% 0.22/0.60    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f31])).
% 0.22/0.60  fof(f160,plain,(
% 0.22/0.60    k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | spl3_9),
% 0.22/0.60    inference(avatar_component_clause,[],[f159])).
% 0.22/0.60  fof(f167,plain,(
% 0.22/0.60    ~spl3_3 | ~spl3_4 | spl3_7),
% 0.22/0.60    inference(avatar_split_clause,[],[f166,f151,f129,f125])).
% 0.22/0.60  fof(f166,plain,(
% 0.22/0.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_7),
% 0.22/0.60    inference(resolution,[],[f153,f70])).
% 0.22/0.60  fof(f70,plain,(
% 0.22/0.60    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(flattening,[],[f26])).
% 0.22/0.60  fof(f26,plain,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.22/0.60  fof(f153,plain,(
% 0.22/0.60    ~v1_funct_1(k2_funct_1(sK2)) | spl3_7),
% 0.22/0.60    inference(avatar_component_clause,[],[f151])).
% 0.22/0.60  fof(f165,plain,(
% 0.22/0.60    ~spl3_3 | ~spl3_4 | spl3_6),
% 0.22/0.60    inference(avatar_split_clause,[],[f163,f147,f129,f125])).
% 0.22/0.60  fof(f163,plain,(
% 0.22/0.60    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_6),
% 0.22/0.60    inference(resolution,[],[f149,f69])).
% 0.22/0.60  fof(f69,plain,(
% 0.22/0.60    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f27])).
% 0.22/0.60  fof(f149,plain,(
% 0.22/0.60    ~v1_relat_1(k2_funct_1(sK2)) | spl3_6),
% 0.22/0.60    inference(avatar_component_clause,[],[f147])).
% 0.22/0.60  fof(f141,plain,(
% 0.22/0.60    spl3_3),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f140])).
% 0.22/0.60  fof(f140,plain,(
% 0.22/0.60    $false | spl3_3),
% 0.22/0.60    inference(resolution,[],[f137,f107])).
% 0.22/0.60  fof(f137,plain,(
% 0.22/0.60    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_3),
% 0.22/0.60    inference(resolution,[],[f127,f78])).
% 0.22/0.60  fof(f78,plain,(
% 0.22/0.60    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f36])).
% 0.22/0.60  fof(f36,plain,(
% 0.22/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.60    inference(ennf_transformation,[],[f7])).
% 0.22/0.60  fof(f7,axiom,(
% 0.22/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.60  fof(f127,plain,(
% 0.22/0.60    ~v1_relat_1(sK2) | spl3_3),
% 0.22/0.60    inference(avatar_component_clause,[],[f125])).
% 0.22/0.60  fof(f139,plain,(
% 0.22/0.60    spl3_4),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f138])).
% 0.22/0.60  fof(f138,plain,(
% 0.22/0.60    $false | spl3_4),
% 0.22/0.60    inference(resolution,[],[f131,f57])).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    v1_funct_1(sK2)),
% 0.22/0.60    inference(cnf_transformation,[],[f52])).
% 0.22/0.60  fof(f131,plain,(
% 0.22/0.60    ~v1_funct_1(sK2) | spl3_4),
% 0.22/0.60    inference(avatar_component_clause,[],[f129])).
% 0.22/0.60  fof(f136,plain,(
% 0.22/0.60    ~spl3_3 | ~spl3_4 | spl3_5),
% 0.22/0.60    inference(avatar_split_clause,[],[f122,f133,f129,f125])).
% 0.22/0.60  fof(f122,plain,(
% 0.22/0.60    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.22/0.60    inference(resolution,[],[f71,f61])).
% 0.22/0.60  fof(f71,plain,(
% 0.22/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f29])).
% 0.22/0.60  fof(f29,plain,(
% 0.22/0.60    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.60    inference(flattening,[],[f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f6])).
% 0.22/0.60  fof(f6,axiom,(
% 0.22/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.22/0.60  fof(f121,plain,(
% 0.22/0.60    spl3_1),
% 0.22/0.60    inference(avatar_contradiction_clause,[],[f120])).
% 0.22/0.60  fof(f120,plain,(
% 0.22/0.60    $false | spl3_1),
% 0.22/0.60    inference(resolution,[],[f114,f56])).
% 0.22/0.60  fof(f114,plain,(
% 0.22/0.60    ~l1_struct_0(sK1) | spl3_1),
% 0.22/0.60    inference(avatar_component_clause,[],[f112])).
% 0.22/0.60  fof(f112,plain,(
% 0.22/0.60    spl3_1 <=> l1_struct_0(sK1)),
% 0.22/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.60  fof(f119,plain,(
% 0.22/0.60    ~spl3_1 | ~spl3_2),
% 0.22/0.60    inference(avatar_split_clause,[],[f110,f116,f112])).
% 0.22/0.60  fof(f110,plain,(
% 0.22/0.60    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 0.22/0.60    inference(forward_demodulation,[],[f109,f100])).
% 0.22/0.60  fof(f109,plain,(
% 0.22/0.60    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 0.22/0.60    inference(resolution,[],[f68,f55])).
% 0.22/0.60  fof(f55,plain,(
% 0.22/0.60    ~v2_struct_0(sK1)),
% 0.22/0.60    inference(cnf_transformation,[],[f52])).
% 0.22/0.60  fof(f68,plain,(
% 0.22/0.60    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.22/0.60    inference(cnf_transformation,[],[f25])).
% 0.22/0.60  fof(f25,plain,(
% 0.22/0.60    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.60    inference(flattening,[],[f24])).
% 0.22/0.60  fof(f24,plain,(
% 0.22/0.60    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,axiom,(
% 0.22/0.60    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.60  % SZS output end Proof for theBenchmark
% 0.22/0.60  % (14676)------------------------------
% 0.22/0.60  % (14676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (14676)Termination reason: Refutation
% 0.22/0.60  
% 0.22/0.60  % (14676)Memory used [KB]: 6396
% 0.22/0.60  % (14676)Time elapsed: 0.134 s
% 0.22/0.60  % (14676)------------------------------
% 0.22/0.60  % (14676)------------------------------
% 1.58/0.60  % (14663)Success in time 0.231 s
%------------------------------------------------------------------------------
