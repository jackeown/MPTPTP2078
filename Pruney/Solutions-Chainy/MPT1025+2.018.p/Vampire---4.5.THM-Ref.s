%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 663 expanded)
%              Number of leaves         :   25 ( 193 expanded)
%              Depth                    :   22
%              Number of atoms          :  529 (3350 expanded)
%              Number of equality atoms :   27 ( 463 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f411,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f180,f181,f182,f190,f218,f410])).

fof(f410,plain,
    ( ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl11_6
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f408,f247])).

fof(f247,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f244,f127])).

fof(f127,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f120,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
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

fof(f120,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f115,f89])).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f33,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

% (4654)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f15,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f115,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f93,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f93,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f56,f87])).

fof(f87,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f55,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f56,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f34])).

% (4676)Refutation not found, incomplete strategy% (4676)------------------------------
% (4676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f244,plain,
    ( v1_xboole_0(sK2)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_6 ),
    inference(resolution,[],[f221,f93])).

fof(f221,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) )
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f166,f186])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f157,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f157,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f153,f55])).

fof(f153,plain,(
    ! [X0] :
      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f80,f87])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f166,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl11_6
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f408,plain,
    ( ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_7
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f407,f232])).

fof(f232,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f230,f127])).

fof(f230,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl11_8 ),
    inference(resolution,[],[f219,f93])).

fof(f219,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | r2_hidden(sK5(X5,sK0,sK3,X6),X5) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f178,f186])).

fof(f178,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK5(X5,sK0,sK3,X6),X5) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl11_8
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK5(X5,sK0,sK3,X6),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f407,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_7 ),
    inference(trivial_inequality_removal,[],[f406])).

fof(f406,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_7 ),
    inference(superposition,[],[f57,f308])).

fof(f308,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f307,f89])).

fof(f307,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f301,f54])).

fof(f54,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f301,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl11_7 ),
    inference(resolution,[],[f256,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f25])).

% (4669)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f256,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f253,f127])).

fof(f253,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl11_7 ),
    inference(resolution,[],[f220,f93])).

fof(f220,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f172,f186])).

fof(f172,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl11_7
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f57,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f218,plain,(
    ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f215,f163])).

fof(f163,plain,
    ( v1_xboole_0(sK0)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl11_5
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f215,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(resolution,[],[f213,f62])).

fof(f213,plain,(
    r2_hidden(sK6(k1_relat_1(sK3)),sK0) ),
    inference(resolution,[],[f137,f135])).

fof(f135,plain,(
    r2_hidden(sK6(k1_relat_1(sK3)),k1_relat_1(sK3)) ),
    inference(resolution,[],[f131,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK6(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f131,plain,(
    ~ v1_xboole_0(k1_relat_1(sK3)) ),
    inference(resolution,[],[f118,f62])).

fof(f118,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f113,f89])).

fof(f113,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f93,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f137,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK3))
      | r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f122,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f122,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f121,f89])).

fof(f121,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f88,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

% (4658)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f88,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f55,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f190,plain,(
    ~ spl11_1 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl11_1 ),
    inference(resolution,[],[f188,f117])).

fof(f117,plain,(
    ~ sP10(k9_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f93,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP10(X1) ) ),
    inference(general_splitting,[],[f79,f85_D])).

fof(f85,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP10(X1) ) ),
    inference(cnf_transformation,[],[f85_D])).

fof(f85_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP10(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f188,plain,
    ( ! [X2] : sP10(k9_relat_1(sK3,X2))
    | ~ spl11_1 ),
    inference(subsumption_resolution,[],[f187,f98])).

fof(f98,plain,
    ( v1_xboole_0(sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl11_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f187,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(sK1)
      | sP10(k9_relat_1(sK3,X2)) ) ),
    inference(resolution,[],[f157,f85])).

fof(f182,plain,
    ( spl11_1
    | spl11_5
    | spl11_6 ),
    inference(avatar_split_clause,[],[f158,f165,f161,f96])).

fof(f158,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f154,f55])).

fof(f154,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f58,f87])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK5(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK5(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK5(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK5(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

% (4670)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (4659)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (4663)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (4684)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (4674)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f181,plain,
    ( spl11_1
    | spl11_5
    | spl11_7 ),
    inference(avatar_split_clause,[],[f168,f171,f161,f96])).

fof(f168,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f155,f55])).

fof(f155,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f59,f87])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f180,plain,
    ( spl11_1
    | spl11_5
    | spl11_8 ),
    inference(avatar_split_clause,[],[f174,f177,f161,f96])).

fof(f174,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f156,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f60,f87])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (4662)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (4676)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (4656)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (4662)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (4664)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (4664)Refutation not found, incomplete strategy% (4664)------------------------------
% 0.20/0.51  % (4664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (4664)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (4664)Memory used [KB]: 10618
% 0.20/0.51  % (4664)Time elapsed: 0.093 s
% 0.20/0.51  % (4664)------------------------------
% 0.20/0.51  % (4664)------------------------------
% 0.20/0.51  % (4668)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.51  % (4657)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f411,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f180,f181,f182,f190,f218,f410])).
% 0.20/0.51  fof(f410,plain,(
% 0.20/0.51    ~spl11_6 | ~spl11_7 | ~spl11_8),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f409])).
% 0.20/0.51  fof(f409,plain,(
% 0.20/0.51    $false | (~spl11_6 | ~spl11_7 | ~spl11_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f408,f247])).
% 0.20/0.51  fof(f247,plain,(
% 0.20/0.51    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f244,f127])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ~v1_xboole_0(sK2)),
% 0.20/0.51    inference(resolution,[],[f120,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f40,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(rectify,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(nnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f115,f89])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    v1_relat_1(sK3)),
% 0.20/0.51    inference(resolution,[],[f55,f73])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f33,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.20/0.51    inference(ennf_transformation,[],[f15])).
% 0.20/0.51  % (4654)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 0.20/0.51    inference(resolution,[],[f93,f71])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f49,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(rectify,[],[f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.20/0.51    inference(backward_demodulation,[],[f56,f87])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 0.20/0.51    inference(resolution,[],[f55,f81])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  % (4676)Refutation not found, incomplete strategy% (4676)------------------------------
% 0.20/0.51  % (4676)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f244,plain,(
% 0.20/0.51    v1_xboole_0(sK2) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_6),
% 0.20/0.51    inference(resolution,[],[f221,f93])).
% 0.20/0.51  fof(f221,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)) ) | ~spl11_6),
% 0.20/0.51    inference(subsumption_resolution,[],[f166,f186])).
% 0.20/0.51  fof(f186,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | m1_subset_1(X0,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f157,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f153,f55])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.51    inference(superposition,[],[f80,f87])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)) ) | ~spl11_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f165])).
% 0.20/0.51  fof(f165,plain,(
% 0.20/0.51    spl11_6 <=> ! [X1,X2] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.20/0.51  fof(f408,plain,(
% 0.20/0.51    ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | (~spl11_7 | ~spl11_8)),
% 0.20/0.51    inference(subsumption_resolution,[],[f407,f232])).
% 0.20/0.51  fof(f232,plain,(
% 0.20/0.51    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~spl11_8),
% 0.20/0.51    inference(subsumption_resolution,[],[f230,f127])).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    v1_xboole_0(sK2) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~spl11_8),
% 0.20/0.51    inference(resolution,[],[f219,f93])).
% 0.20/0.51  fof(f219,plain,(
% 0.20/0.51    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | r2_hidden(sK5(X5,sK0,sK3,X6),X5)) ) | ~spl11_8),
% 0.20/0.51    inference(subsumption_resolution,[],[f178,f186])).
% 0.20/0.51  fof(f178,plain,(
% 0.20/0.51    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK5(X5,sK0,sK3,X6),X5)) ) | ~spl11_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f177])).
% 0.20/0.51  fof(f177,plain,(
% 0.20/0.51    spl11_8 <=> ! [X5,X6] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK5(X5,sK0,sK3,X6),X5))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 0.20/0.51  fof(f407,plain,(
% 0.20/0.51    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_7),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f406])).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    sK4 != sK4 | ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_7),
% 0.20/0.51    inference(superposition,[],[f57,f308])).
% 0.20/0.51  fof(f308,plain,(
% 0.20/0.51    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~spl11_7),
% 0.20/0.51    inference(subsumption_resolution,[],[f307,f89])).
% 0.20/0.51  fof(f307,plain,(
% 0.20/0.51    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl11_7),
% 0.20/0.51    inference(subsumption_resolution,[],[f301,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f301,plain,(
% 0.20/0.51    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl11_7),
% 0.20/0.51    inference(resolution,[],[f256,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(nnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f25])).
% 0.20/0.51  % (4669)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.20/0.51  fof(f256,plain,(
% 0.20/0.51    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl11_7),
% 0.20/0.51    inference(subsumption_resolution,[],[f253,f127])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    v1_xboole_0(sK2) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl11_7),
% 0.20/0.51    inference(resolution,[],[f220,f93])).
% 0.20/0.51  fof(f220,plain,(
% 0.20/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)) ) | ~spl11_7),
% 0.20/0.51    inference(subsumption_resolution,[],[f172,f186])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)) ) | ~spl11_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f171])).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl11_7 <=> ! [X3,X4] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f34])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    ~spl11_5),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    $false | ~spl11_5),
% 0.20/0.51    inference(subsumption_resolution,[],[f215,f163])).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    v1_xboole_0(sK0) | ~spl11_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f161])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl11_5 <=> v1_xboole_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    ~v1_xboole_0(sK0)),
% 0.20/0.51    inference(resolution,[],[f213,f62])).
% 0.20/0.51  fof(f213,plain,(
% 0.20/0.51    r2_hidden(sK6(k1_relat_1(sK3)),sK0)),
% 0.20/0.51    inference(resolution,[],[f137,f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    r2_hidden(sK6(k1_relat_1(sK3)),k1_relat_1(sK3))),
% 0.20/0.51    inference(resolution,[],[f131,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f42])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ~v1_xboole_0(k1_relat_1(sK3))),
% 0.20/0.51    inference(resolution,[],[f118,f62])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.20/0.51    inference(subsumption_resolution,[],[f113,f89])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.20/0.51    inference(resolution,[],[f93,f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f51])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(X0,sK0)) )),
% 0.20/0.51    inference(resolution,[],[f122,f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(nnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    r1_tarski(k1_relat_1(sK3),sK0)),
% 0.20/0.51    inference(subsumption_resolution,[],[f121,f89])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.20/0.51    inference(resolution,[],[f88,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(nnf_transformation,[],[f20])).
% 0.20/0.51  % (4658)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    v4_relat_1(sK3,sK0)),
% 0.20/0.51    inference(resolution,[],[f55,f74])).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.20/0.51    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    ~spl11_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f189])).
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    $false | ~spl11_1),
% 0.20/0.51    inference(resolution,[],[f188,f117])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ~sP10(k9_relat_1(sK3,sK2))),
% 0.20/0.51    inference(resolution,[],[f93,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP10(X1)) )),
% 0.20/0.52    inference(general_splitting,[],[f79,f85_D])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP10(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f85_D])).
% 0.20/0.52  fof(f85_D,plain,(
% 0.20/0.52    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP10(X1)) )),
% 0.20/0.52    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    ( ! [X2] : (sP10(k9_relat_1(sK3,X2))) ) | ~spl11_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f187,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | ~spl11_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f96])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl11_1 <=> v1_xboole_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    ( ! [X2] : (~v1_xboole_0(sK1) | sP10(k9_relat_1(sK3,X2))) )),
% 0.20/0.52    inference(resolution,[],[f157,f85])).
% 0.20/0.52  fof(f182,plain,(
% 0.20/0.52    spl11_1 | spl11_5 | spl11_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f158,f165,f161,f96])).
% 0.20/0.52  fof(f158,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f154,f55])).
% 0.20/0.52  fof(f154,plain,(
% 0.20/0.52    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f58,f87])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.52    inference(rectify,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  % (4670)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (4659)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (4663)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (4684)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (4674)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    spl11_1 | spl11_5 | spl11_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f168,f171,f161,f96])).
% 0.20/0.52  fof(f168,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f155,f55])).
% 0.20/0.52  fof(f155,plain,(
% 0.20/0.52    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f59,f87])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    spl11_1 | spl11_5 | spl11_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f174,f177,f161,f96])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f156,f55])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 0.20/0.52    inference(superposition,[],[f60,f87])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | r2_hidden(sK5(X1,X2,X3,X4),X1) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (4662)------------------------------
% 0.20/0.52  % (4662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (4662)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (4662)Memory used [KB]: 10874
% 0.20/0.52  % (4662)Time elapsed: 0.095 s
% 0.20/0.52  % (4662)------------------------------
% 0.20/0.52  % (4662)------------------------------
% 0.20/0.53  % (4675)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (4653)Success in time 0.168 s
%------------------------------------------------------------------------------
