%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:30 EST 2020

% Result     : Theorem 1.65s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 238 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :  277 ( 976 expanded)
%              Number of equality atoms :   26 ( 140 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f171,f173,f197,f200])).

fof(f200,plain,
    ( ~ spl5_1
    | spl5_3
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | ~ spl5_1
    | spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f198,f116])).

fof(f116,plain,
    ( ~ v1_xboole_0(sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl5_3
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f198,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f186,f120])).

fof(f120,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f186,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

fof(f101,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f197,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f195,f72])).

fof(f72,plain,(
    k1_xboole_0 != k1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f71,f42])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X3,sK1) )
    & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ! [X3] :
                    ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                    | ~ m1_subset_1(X3,X1) )
                & k1_xboole_0 != k1_relset_1(X0,X1,X2)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ! [X3] :
                ( ~ r2_hidden(X3,k2_relset_1(sK0,X1,X2))
                | ~ m1_subset_1(X3,X1) )
            & k1_xboole_0 != k1_relset_1(sK0,X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
              | ~ m1_subset_1(X3,sK1) )
          & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ! [X3] :
            ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,X2))
            | ~ m1_subset_1(X3,sK1) )
        & k1_xboole_0 != k1_relset_1(sK0,sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
   => ( ! [X3] :
          ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
          | ~ m1_subset_1(X3,sK1) )
      & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

fof(f71,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f43,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f43,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f195,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f179,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f179,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl5_3 ),
    inference(resolution,[],[f117,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f117,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f173,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f172,f103,f119,f115])).

fof(f103,plain,
    ( spl5_2
  <=> r2_hidden(sK3(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f172,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f136,f132])).

fof(f132,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f109,f113])).

fof(f113,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f109,f45])).

fof(f109,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f107,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f107,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f105,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relat_1(sK2)) ) ),
    inference(backward_demodulation,[],[f61,f73])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f61,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(resolution,[],[f52,f44])).

fof(f44,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK1)
      | ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f105,plain,
    ( r2_hidden(sK3(k2_relat_1(sK2)),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f136,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl5_2 ),
    inference(superposition,[],[f47,f113])).

fof(f171,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f123,f42])).

fof(f123,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_4 ),
    inference(resolution,[],[f121,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f119])).

fof(f106,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f96,f103,f99])).

fof(f96,plain,
    ( r2_hidden(sK3(k2_relat_1(sK2)),sK1)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(resolution,[],[f95,f42])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
      | r2_hidden(sK3(k2_relat_1(X0)),X1)
      | v1_xboole_0(k2_relat_1(X0)) ) ),
    inference(condensation,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_xboole_0(k2_relat_1(X0))
      | r2_hidden(sK3(k2_relat_1(X0)),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) ) ),
    inference(resolution,[],[f85,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_relat_1(X0,X1)
      | v1_xboole_0(k2_relat_1(X0))
      | r2_hidden(sK3(k2_relat_1(X0)),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f66,f56])).

fof(f66,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | v1_xboole_0(k2_relat_1(X2))
      | ~ v5_relat_1(X2,X3)
      | r2_hidden(sK3(k2_relat_1(X2)),X3) ) ),
    inference(resolution,[],[f64,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(sK3(X0),X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f53,f49])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.53  % (26253)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (26276)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (26271)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (26263)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (26276)Refutation not found, incomplete strategy% (26276)------------------------------
% 0.21/0.55  % (26276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26271)Refutation not found, incomplete strategy% (26271)------------------------------
% 0.21/0.55  % (26271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (26271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26271)Memory used [KB]: 10618
% 0.21/0.55  % (26271)Time elapsed: 0.127 s
% 0.21/0.55  % (26271)------------------------------
% 0.21/0.55  % (26271)------------------------------
% 0.21/0.55  % (26276)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (26276)Memory used [KB]: 10746
% 0.21/0.55  % (26276)Time elapsed: 0.129 s
% 0.21/0.55  % (26276)------------------------------
% 0.21/0.55  % (26276)------------------------------
% 1.36/0.56  % (26263)Refutation not found, incomplete strategy% (26263)------------------------------
% 1.36/0.56  % (26263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.56  % (26263)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.56  
% 1.36/0.56  % (26263)Memory used [KB]: 10618
% 1.36/0.56  % (26263)Time elapsed: 0.134 s
% 1.36/0.56  % (26263)------------------------------
% 1.36/0.56  % (26263)------------------------------
% 1.36/0.56  % (26256)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.57  % (26272)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.65/0.58  % (26261)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.65/0.58  % (26261)Refutation not found, incomplete strategy% (26261)------------------------------
% 1.65/0.58  % (26261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (26261)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.58  
% 1.65/0.58  % (26261)Memory used [KB]: 10746
% 1.65/0.58  % (26261)Time elapsed: 0.140 s
% 1.65/0.58  % (26261)------------------------------
% 1.65/0.58  % (26261)------------------------------
% 1.65/0.58  % (26280)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.65/0.59  % (26256)Refutation found. Thanks to Tanya!
% 1.65/0.59  % SZS status Theorem for theBenchmark
% 1.65/0.59  % SZS output start Proof for theBenchmark
% 1.65/0.59  fof(f201,plain,(
% 1.65/0.59    $false),
% 1.65/0.59    inference(avatar_sat_refutation,[],[f106,f171,f173,f197,f200])).
% 1.65/0.59  fof(f200,plain,(
% 1.65/0.59    ~spl5_1 | spl5_3 | ~spl5_4),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f199])).
% 1.65/0.59  fof(f199,plain,(
% 1.65/0.59    $false | (~spl5_1 | spl5_3 | ~spl5_4)),
% 1.65/0.59    inference(subsumption_resolution,[],[f198,f116])).
% 1.65/0.59  fof(f116,plain,(
% 1.65/0.59    ~v1_xboole_0(sK2) | spl5_3),
% 1.65/0.59    inference(avatar_component_clause,[],[f115])).
% 1.65/0.59  fof(f115,plain,(
% 1.65/0.59    spl5_3 <=> v1_xboole_0(sK2)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.65/0.59  fof(f198,plain,(
% 1.65/0.59    v1_xboole_0(sK2) | (~spl5_1 | ~spl5_4)),
% 1.65/0.59    inference(subsumption_resolution,[],[f186,f120])).
% 1.65/0.59  fof(f120,plain,(
% 1.65/0.59    v1_relat_1(sK2) | ~spl5_4),
% 1.65/0.59    inference(avatar_component_clause,[],[f119])).
% 1.65/0.59  fof(f119,plain,(
% 1.65/0.59    spl5_4 <=> v1_relat_1(sK2)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.65/0.59  fof(f186,plain,(
% 1.65/0.59    ~v1_relat_1(sK2) | v1_xboole_0(sK2) | ~spl5_1),
% 1.65/0.59    inference(resolution,[],[f101,f47])).
% 1.65/0.59  fof(f47,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f19])).
% 1.65/0.59  fof(f19,plain,(
% 1.65/0.59    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.65/0.59    inference(flattening,[],[f18])).
% 1.65/0.59  fof(f18,plain,(
% 1.65/0.59    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f7])).
% 1.65/0.59  fof(f7,axiom,(
% 1.65/0.59    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).
% 1.65/0.59  fof(f101,plain,(
% 1.65/0.59    v1_xboole_0(k2_relat_1(sK2)) | ~spl5_1),
% 1.65/0.59    inference(avatar_component_clause,[],[f99])).
% 1.65/0.59  fof(f99,plain,(
% 1.65/0.59    spl5_1 <=> v1_xboole_0(k2_relat_1(sK2))),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.65/0.59  fof(f197,plain,(
% 1.65/0.59    ~spl5_3),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f196])).
% 1.65/0.59  fof(f196,plain,(
% 1.65/0.59    $false | ~spl5_3),
% 1.65/0.59    inference(subsumption_resolution,[],[f195,f72])).
% 1.65/0.59  fof(f72,plain,(
% 1.65/0.59    k1_xboole_0 != k1_relat_1(sK2)),
% 1.65/0.59    inference(subsumption_resolution,[],[f71,f42])).
% 1.65/0.59  fof(f42,plain,(
% 1.65/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.59    inference(cnf_transformation,[],[f30])).
% 1.65/0.59  fof(f30,plain,(
% 1.65/0.59    ((! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f29,f28,f27])).
% 1.65/0.59  fof(f27,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f28,plain,(
% 1.65/0.59    ? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(sK0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) & ~v1_xboole_0(X1)) => (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) & ~v1_xboole_0(sK1))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f29,plain,(
% 1.65/0.59    ? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,X2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) => (! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) & k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f15,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.65/0.59    inference(flattening,[],[f14])).
% 1.65/0.59  fof(f14,plain,(
% 1.65/0.59    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f13])).
% 1.65/0.59  fof(f13,negated_conjecture,(
% 1.65/0.59    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.65/0.59    inference(negated_conjecture,[],[f12])).
% 1.65/0.59  fof(f12,conjecture,(
% 1.65/0.59    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).
% 1.65/0.59  fof(f71,plain,(
% 1.65/0.59    k1_xboole_0 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.65/0.59    inference(superposition,[],[f43,f57])).
% 1.65/0.59  fof(f57,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f24])).
% 1.65/0.59  fof(f24,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f10])).
% 1.65/0.59  fof(f10,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.65/0.59  fof(f43,plain,(
% 1.65/0.59    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 1.65/0.59    inference(cnf_transformation,[],[f30])).
% 1.65/0.59  fof(f195,plain,(
% 1.65/0.59    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_3),
% 1.65/0.59    inference(resolution,[],[f179,f45])).
% 1.65/0.59  fof(f45,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.65/0.59    inference(cnf_transformation,[],[f16])).
% 1.65/0.59  fof(f16,plain,(
% 1.65/0.59    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f3])).
% 1.65/0.59  fof(f3,axiom,(
% 1.65/0.59    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.65/0.59  fof(f179,plain,(
% 1.65/0.59    v1_xboole_0(k1_relat_1(sK2)) | ~spl5_3),
% 1.65/0.59    inference(resolution,[],[f117,f46])).
% 1.65/0.59  fof(f46,plain,(
% 1.65/0.59    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f17])).
% 1.65/0.59  fof(f17,plain,(
% 1.65/0.59    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.65/0.59    inference(ennf_transformation,[],[f6])).
% 1.65/0.59  fof(f6,axiom,(
% 1.65/0.59    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.65/0.59  fof(f117,plain,(
% 1.65/0.59    v1_xboole_0(sK2) | ~spl5_3),
% 1.65/0.59    inference(avatar_component_clause,[],[f115])).
% 1.65/0.59  fof(f173,plain,(
% 1.65/0.59    spl5_3 | ~spl5_4 | ~spl5_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f172,f103,f119,f115])).
% 1.65/0.59  fof(f103,plain,(
% 1.65/0.59    spl5_2 <=> r2_hidden(sK3(k2_relat_1(sK2)),sK1)),
% 1.65/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.65/0.59  fof(f172,plain,(
% 1.65/0.59    ~v1_relat_1(sK2) | v1_xboole_0(sK2) | ~spl5_2),
% 1.65/0.59    inference(subsumption_resolution,[],[f136,f132])).
% 1.65/0.59  fof(f132,plain,(
% 1.65/0.59    v1_xboole_0(k1_xboole_0) | ~spl5_2),
% 1.65/0.59    inference(backward_demodulation,[],[f109,f113])).
% 1.65/0.59  fof(f113,plain,(
% 1.65/0.59    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_2),
% 1.65/0.59    inference(resolution,[],[f109,f45])).
% 1.65/0.59  fof(f109,plain,(
% 1.65/0.59    v1_xboole_0(k2_relat_1(sK2)) | ~spl5_2),
% 1.65/0.59    inference(resolution,[],[f107,f49])).
% 1.65/0.59  fof(f49,plain,(
% 1.65/0.59    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f34])).
% 1.65/0.59  fof(f34,plain,(
% 1.65/0.59    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK3(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f32,f33])).
% 1.65/0.59  fof(f33,plain,(
% 1.65/0.59    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f32,plain,(
% 1.65/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.65/0.59    inference(rectify,[],[f31])).
% 1.65/0.59  fof(f31,plain,(
% 1.65/0.59    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.65/0.59    inference(nnf_transformation,[],[f1])).
% 1.65/0.59  fof(f1,axiom,(
% 1.65/0.59    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.65/0.59  fof(f107,plain,(
% 1.65/0.59    ~r2_hidden(sK3(k2_relat_1(sK2)),k2_relat_1(sK2)) | ~spl5_2),
% 1.65/0.59    inference(resolution,[],[f105,f77])).
% 1.65/0.59  fof(f77,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relat_1(sK2))) )),
% 1.65/0.59    inference(backward_demodulation,[],[f61,f73])).
% 1.65/0.59  fof(f73,plain,(
% 1.65/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.65/0.59    inference(resolution,[],[f58,f42])).
% 1.65/0.59  fof(f58,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f25])).
% 1.65/0.59  fof(f25,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f11])).
% 1.65/0.59  fof(f11,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.65/0.59  fof(f61,plain,(
% 1.65/0.59    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,k2_relset_1(sK0,sK1,sK2))) )),
% 1.65/0.59    inference(resolution,[],[f52,f44])).
% 1.65/0.59  fof(f44,plain,(
% 1.65/0.59    ( ! [X3] : (~m1_subset_1(X3,sK1) | ~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f30])).
% 1.65/0.59  fof(f52,plain,(
% 1.65/0.59    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f21])).
% 1.65/0.59  fof(f21,plain,(
% 1.65/0.59    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f4])).
% 1.65/0.59  fof(f4,axiom,(
% 1.65/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.65/0.59  fof(f105,plain,(
% 1.65/0.59    r2_hidden(sK3(k2_relat_1(sK2)),sK1) | ~spl5_2),
% 1.65/0.59    inference(avatar_component_clause,[],[f103])).
% 1.65/0.59  fof(f136,plain,(
% 1.65/0.59    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK2) | v1_xboole_0(sK2) | ~spl5_2),
% 1.65/0.59    inference(superposition,[],[f47,f113])).
% 1.65/0.59  fof(f171,plain,(
% 1.65/0.59    spl5_4),
% 1.65/0.59    inference(avatar_contradiction_clause,[],[f169])).
% 1.65/0.59  fof(f169,plain,(
% 1.65/0.59    $false | spl5_4),
% 1.65/0.59    inference(resolution,[],[f123,f42])).
% 1.65/0.59  fof(f123,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_4),
% 1.65/0.59    inference(resolution,[],[f121,f56])).
% 1.65/0.59  fof(f56,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f23])).
% 1.65/0.59  fof(f23,plain,(
% 1.65/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f8])).
% 1.65/0.59  fof(f8,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.59  fof(f121,plain,(
% 1.65/0.59    ~v1_relat_1(sK2) | spl5_4),
% 1.65/0.59    inference(avatar_component_clause,[],[f119])).
% 1.65/0.59  fof(f106,plain,(
% 1.65/0.59    spl5_1 | spl5_2),
% 1.65/0.59    inference(avatar_split_clause,[],[f96,f103,f99])).
% 1.65/0.59  fof(f96,plain,(
% 1.65/0.59    r2_hidden(sK3(k2_relat_1(sK2)),sK1) | v1_xboole_0(k2_relat_1(sK2))),
% 1.65/0.59    inference(resolution,[],[f95,f42])).
% 1.65/0.59  fof(f95,plain,(
% 1.65/0.59    ( ! [X4,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | r2_hidden(sK3(k2_relat_1(X0)),X1) | v1_xboole_0(k2_relat_1(X0))) )),
% 1.65/0.59    inference(condensation,[],[f94])).
% 1.65/0.59  fof(f94,plain,(
% 1.65/0.59    ( ! [X4,X2,X0,X3,X1] : (v1_xboole_0(k2_relat_1(X0)) | r2_hidden(sK3(k2_relat_1(X0)),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))) )),
% 1.65/0.59    inference(resolution,[],[f85,f60])).
% 1.65/0.59  fof(f60,plain,(
% 1.65/0.59    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.65/0.59    inference(cnf_transformation,[],[f26])).
% 1.65/0.59  fof(f26,plain,(
% 1.65/0.59    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.59    inference(ennf_transformation,[],[f9])).
% 1.65/0.59  fof(f9,axiom,(
% 1.65/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.65/0.59  fof(f85,plain,(
% 1.65/0.59    ( ! [X2,X0,X3,X1] : (~v5_relat_1(X0,X1) | v1_xboole_0(k2_relat_1(X0)) | r2_hidden(sK3(k2_relat_1(X0)),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.65/0.59    inference(resolution,[],[f66,f56])).
% 1.65/0.59  fof(f66,plain,(
% 1.65/0.59    ( ! [X2,X3] : (~v1_relat_1(X2) | v1_xboole_0(k2_relat_1(X2)) | ~v5_relat_1(X2,X3) | r2_hidden(sK3(k2_relat_1(X2)),X3)) )),
% 1.65/0.59    inference(resolution,[],[f64,f50])).
% 1.65/0.59  fof(f50,plain,(
% 1.65/0.59    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f35])).
% 1.65/0.59  fof(f35,plain,(
% 1.65/0.59    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.65/0.59    inference(nnf_transformation,[],[f20])).
% 1.65/0.59  fof(f20,plain,(
% 1.65/0.59    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.65/0.59    inference(ennf_transformation,[],[f5])).
% 1.65/0.59  fof(f5,axiom,(
% 1.65/0.59    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.65/0.59  fof(f64,plain,(
% 1.65/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(sK3(X0),X1) | v1_xboole_0(X0)) )),
% 1.65/0.59    inference(resolution,[],[f53,f49])).
% 1.65/0.59  fof(f53,plain,(
% 1.65/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.65/0.59    inference(cnf_transformation,[],[f39])).
% 1.65/0.59  fof(f39,plain,(
% 1.65/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.65/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.65/0.59  fof(f38,plain,(
% 1.65/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.65/0.59    introduced(choice_axiom,[])).
% 1.65/0.59  fof(f37,plain,(
% 1.65/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.65/0.59    inference(rectify,[],[f36])).
% 1.65/0.59  fof(f36,plain,(
% 1.65/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.65/0.59    inference(nnf_transformation,[],[f22])).
% 1.65/0.59  fof(f22,plain,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.65/0.59    inference(ennf_transformation,[],[f2])).
% 1.65/0.59  fof(f2,axiom,(
% 1.65/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.65/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.65/0.59  % SZS output end Proof for theBenchmark
% 1.65/0.59  % (26256)------------------------------
% 1.65/0.59  % (26256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (26256)Termination reason: Refutation
% 1.65/0.59  
% 1.65/0.59  % (26256)Memory used [KB]: 10746
% 1.65/0.59  % (26256)Time elapsed: 0.146 s
% 1.65/0.59  % (26256)------------------------------
% 1.65/0.59  % (26256)------------------------------
% 1.65/0.59  % (26251)Success in time 0.225 s
%------------------------------------------------------------------------------
