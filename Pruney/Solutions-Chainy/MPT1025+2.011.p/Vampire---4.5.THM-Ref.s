%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:22 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 680 expanded)
%              Number of leaves         :   28 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  564 (3428 expanded)
%              Number of equality atoms :   36 ( 469 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f433,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f154,f193,f194,f195,f197,f216,f389,f422])).

fof(f422,plain,
    ( ~ spl11_5
    | ~ spl11_6 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f176,f398])).

fof(f398,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl11_5 ),
    inference(backward_demodulation,[],[f137,f153])).

fof(f153,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl11_5
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f137,plain,(
    ~ v1_xboole_0(k1_relat_1(sK3)) ),
    inference(resolution,[],[f126,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f126,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f122,f101])).

fof(f101,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f61,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f37,f36])).

fof(f36,plain,
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

fof(f37,plain,
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

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f122,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f106,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

fof(f106,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f62,f99])).

fof(f99,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(resolution,[],[f61,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f62,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f176,plain,
    ( v1_xboole_0(sK0)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl11_6
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f389,plain,
    ( ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(avatar_contradiction_clause,[],[f388])).

fof(f388,plain,
    ( $false
    | ~ spl11_7
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f387,f246])).

fof(f246,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f243,f133])).

fof(f133,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f128,f68])).

fof(f128,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    inference(subsumption_resolution,[],[f124,f101])).

fof(f124,plain,
    ( r2_hidden(sK8(sK4,sK2,sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f106,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(sK8(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f243,plain,
    ( v1_xboole_0(sK2)
    | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_7 ),
    inference(resolution,[],[f219,f106])).

fof(f219,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) )
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f179,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f170,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f170,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f166,f61])).

fof(f166,plain,(
    ! [X0] :
      ( m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f89,f99])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f179,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) )
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl11_7
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,sK1)
        | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f387,plain,
    ( ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_8
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f386,f237])).

fof(f237,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f234,f133])).

fof(f234,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl11_9 ),
    inference(resolution,[],[f217,f106])).

fof(f217,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | r2_hidden(sK5(X5,sK0,sK3,X6),X5) )
    | ~ spl11_9 ),
    inference(subsumption_resolution,[],[f191,f201])).

fof(f191,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK5(X5,sK0,sK3,X6),X5) )
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl11_9
  <=> ! [X5,X6] :
        ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
        | v1_xboole_0(X5)
        | ~ m1_subset_1(X6,sK1)
        | r2_hidden(sK5(X5,sK0,sK3,X6),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f386,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_8 ),
    inference(trivial_inequality_removal,[],[f385])).

fof(f385,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl11_8 ),
    inference(superposition,[],[f63,f300])).

fof(f300,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f299,f101])).

fof(f299,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f294,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f294,plain,
    ( sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl11_8 ),
    inference(resolution,[],[f266,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f266,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f262,f133])).

fof(f262,plain,
    ( v1_xboole_0(sK2)
    | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl11_8 ),
    inference(resolution,[],[f218,f106])).

fof(f218,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl11_8 ),
    inference(subsumption_resolution,[],[f185,f201])).

fof(f185,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) )
    | ~ spl11_8 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl11_8
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3)
        | ~ m1_subset_1(X4,sK1)
        | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).

fof(f63,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f216,plain,
    ( spl11_4
    | ~ spl11_6 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl11_4
    | ~ spl11_6 ),
    inference(subsumption_resolution,[],[f214,f176])).

fof(f214,plain,
    ( ~ v1_xboole_0(sK0)
    | spl11_4 ),
    inference(resolution,[],[f165,f68])).

fof(f165,plain,
    ( r2_hidden(sK7(sK0,k1_relat_1(sK3)),sK0)
    | spl11_4 ),
    inference(resolution,[],[f149,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f149,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl11_4
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f197,plain,(
    ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f114,f159])).

fof(f159,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(resolution,[],[f127,f68])).

fof(f127,plain,(
    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f123,f101])).

fof(f123,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f106,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f114,plain,
    ( v1_xboole_0(sK3)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl11_2
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f195,plain,
    ( spl11_1
    | spl11_6
    | spl11_7 ),
    inference(avatar_split_clause,[],[f171,f178,f174,f108])).

fof(f108,plain,
    ( spl11_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f171,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f167,f61])).

fof(f167,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k9_relat_1(sK3,X1))
      | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)
      | ~ m1_subset_1(X2,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f64,f99])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK5(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK5(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
    inference(rectify,[],[f39])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

fof(f194,plain,
    ( spl11_1
    | spl11_6
    | spl11_8 ),
    inference(avatar_split_clause,[],[f181,f184,f174,f108])).

fof(f181,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f168,f61])).

fof(f168,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k9_relat_1(sK3,X3))
      | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)
      | ~ m1_subset_1(X4,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X3)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f65,f99])).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f193,plain,
    ( spl11_1
    | spl11_6
    | spl11_9 ),
    inference(avatar_split_clause,[],[f187,f190,f174,f108])).

fof(f187,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f169,f61])).

fof(f169,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X6,k9_relat_1(sK3,X5))
      | r2_hidden(sK5(X5,sK0,sK3,X6),X5)
      | ~ m1_subset_1(X6,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f66,f99])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f154,plain,
    ( ~ spl11_4
    | spl11_5 ),
    inference(avatar_split_clause,[],[f145,f151,f147])).

fof(f145,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3)) ),
    inference(resolution,[],[f131,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f130,f101])).

fof(f130,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f100,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f100,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f61,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f115,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f102,f112,f108])).

fof(f102,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f61,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:00:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (10454)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (10453)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (10447)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (10464)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (10463)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (10450)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (10446)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (10448)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (10466)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (10464)Refutation not found, incomplete strategy% (10464)------------------------------
% 0.20/0.53  % (10464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (10464)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (10464)Memory used [KB]: 10746
% 0.20/0.53  % (10464)Time elapsed: 0.076 s
% 0.20/0.53  % (10464)------------------------------
% 0.20/0.53  % (10464)------------------------------
% 0.20/0.53  % (10456)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (10460)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (10443)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (10444)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (10445)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (10442)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (10470)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (10444)Refutation not found, incomplete strategy% (10444)------------------------------
% 0.20/0.54  % (10444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (10444)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (10444)Memory used [KB]: 10874
% 0.20/0.54  % (10444)Time elapsed: 0.123 s
% 0.20/0.54  % (10444)------------------------------
% 0.20/0.54  % (10444)------------------------------
% 0.20/0.54  % (10457)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.54  % (10453)Refutation not found, incomplete strategy% (10453)------------------------------
% 1.38/0.54  % (10453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (10453)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (10453)Memory used [KB]: 10618
% 1.38/0.54  % (10453)Time elapsed: 0.126 s
% 1.38/0.54  % (10453)------------------------------
% 1.38/0.54  % (10453)------------------------------
% 1.38/0.54  % (10459)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.54  % (10469)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.38/0.55  % (10467)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (10465)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.55  % (10452)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.55  % (10461)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (10452)Refutation not found, incomplete strategy% (10452)------------------------------
% 1.38/0.55  % (10452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (10471)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (10458)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.55  % (10451)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.55  % (10468)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (10462)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (10449)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.55  % (10450)Refutation found. Thanks to Tanya!
% 1.38/0.55  % SZS status Theorem for theBenchmark
% 1.38/0.55  % SZS output start Proof for theBenchmark
% 1.38/0.55  fof(f433,plain,(
% 1.38/0.55    $false),
% 1.38/0.55    inference(avatar_sat_refutation,[],[f115,f154,f193,f194,f195,f197,f216,f389,f422])).
% 1.38/0.55  fof(f422,plain,(
% 1.38/0.55    ~spl11_5 | ~spl11_6),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f421])).
% 1.38/0.55  fof(f421,plain,(
% 1.38/0.55    $false | (~spl11_5 | ~spl11_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f176,f398])).
% 1.38/0.55  fof(f398,plain,(
% 1.38/0.55    ~v1_xboole_0(sK0) | ~spl11_5),
% 1.38/0.55    inference(backward_demodulation,[],[f137,f153])).
% 1.38/0.55  fof(f153,plain,(
% 1.38/0.55    sK0 = k1_relat_1(sK3) | ~spl11_5),
% 1.38/0.55    inference(avatar_component_clause,[],[f151])).
% 1.38/0.55  fof(f151,plain,(
% 1.38/0.55    spl11_5 <=> sK0 = k1_relat_1(sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 1.38/0.55  fof(f137,plain,(
% 1.38/0.55    ~v1_xboole_0(k1_relat_1(sK3))),
% 1.38/0.55    inference(resolution,[],[f126,f68])).
% 1.38/0.55  fof(f68,plain,(
% 1.38/0.55    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f46])).
% 1.38/0.55  fof(f46,plain,(
% 1.38/0.55    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f45])).
% 1.38/0.55  fof(f45,plain,(
% 1.38/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f44,plain,(
% 1.38/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.55    inference(rectify,[],[f43])).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.38/0.55    inference(nnf_transformation,[],[f1])).
% 1.38/0.55  fof(f1,axiom,(
% 1.38/0.55    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.38/0.55  fof(f126,plain,(
% 1.38/0.55    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.38/0.55    inference(subsumption_resolution,[],[f122,f101])).
% 1.38/0.55  fof(f101,plain,(
% 1.38/0.55    v1_relat_1(sK3)),
% 1.38/0.55    inference(resolution,[],[f61,f83])).
% 1.38/0.55  fof(f83,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f26])).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f8])).
% 1.38/0.55  fof(f8,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.55  fof(f61,plain,(
% 1.38/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.38/0.55    inference(cnf_transformation,[],[f38])).
% 1.38/0.55  fof(f38,plain,(
% 1.38/0.55    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f37,f36])).
% 1.38/0.55  fof(f36,plain,(
% 1.38/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f37,plain,(
% 1.38/0.55    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f20,plain,(
% 1.38/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.38/0.55    inference(flattening,[],[f19])).
% 1.38/0.55  fof(f19,plain,(
% 1.38/0.55    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.38/0.55    inference(ennf_transformation,[],[f17])).
% 1.38/0.55  fof(f17,plain,(
% 1.38/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.38/0.55    inference(pure_predicate_removal,[],[f16])).
% 1.38/0.55  fof(f16,negated_conjecture,(
% 1.38/0.55    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.38/0.55    inference(negated_conjecture,[],[f15])).
% 1.38/0.55  fof(f15,conjecture,(
% 1.38/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 1.38/0.55  fof(f122,plain,(
% 1.38/0.55    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 1.38/0.55    inference(resolution,[],[f106,f79])).
% 1.38/0.55  fof(f79,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f57])).
% 1.38/0.55  fof(f57,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f55,f56])).
% 1.38/0.55  fof(f56,plain,(
% 1.38/0.55    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f55,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(rectify,[],[f54])).
% 1.38/0.55  fof(f54,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(nnf_transformation,[],[f25])).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(ennf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).
% 1.38/0.55  fof(f106,plain,(
% 1.38/0.55    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.38/0.55    inference(backward_demodulation,[],[f62,f99])).
% 1.38/0.55  fof(f99,plain,(
% 1.38/0.55    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.38/0.55    inference(resolution,[],[f61,f90])).
% 1.38/0.55  fof(f90,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f33])).
% 1.38/0.55  fof(f33,plain,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f12])).
% 1.38/0.55  fof(f12,axiom,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.38/0.55  fof(f62,plain,(
% 1.38/0.55    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.38/0.55    inference(cnf_transformation,[],[f38])).
% 1.38/0.55  fof(f176,plain,(
% 1.38/0.55    v1_xboole_0(sK0) | ~spl11_6),
% 1.38/0.55    inference(avatar_component_clause,[],[f174])).
% 1.38/0.55  fof(f174,plain,(
% 1.38/0.55    spl11_6 <=> v1_xboole_0(sK0)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 1.38/0.55  fof(f389,plain,(
% 1.38/0.55    ~spl11_7 | ~spl11_8 | ~spl11_9),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f388])).
% 1.38/0.55  fof(f388,plain,(
% 1.38/0.55    $false | (~spl11_7 | ~spl11_8 | ~spl11_9)),
% 1.38/0.55    inference(subsumption_resolution,[],[f387,f246])).
% 1.38/0.55  fof(f246,plain,(
% 1.38/0.55    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_7),
% 1.38/0.55    inference(subsumption_resolution,[],[f243,f133])).
% 1.38/0.55  fof(f133,plain,(
% 1.38/0.55    ~v1_xboole_0(sK2)),
% 1.38/0.55    inference(resolution,[],[f128,f68])).
% 1.38/0.55  fof(f128,plain,(
% 1.38/0.55    r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 1.38/0.55    inference(subsumption_resolution,[],[f124,f101])).
% 1.38/0.55  fof(f124,plain,(
% 1.38/0.55    r2_hidden(sK8(sK4,sK2,sK3),sK2) | ~v1_relat_1(sK3)),
% 1.38/0.55    inference(resolution,[],[f106,f81])).
% 1.38/0.55  fof(f81,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(sK8(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f57])).
% 1.38/0.55  fof(f243,plain,(
% 1.38/0.55    v1_xboole_0(sK2) | m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_7),
% 1.38/0.55    inference(resolution,[],[f219,f106])).
% 1.38/0.55  fof(f219,plain,(
% 1.38/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)) ) | ~spl11_7),
% 1.38/0.55    inference(subsumption_resolution,[],[f179,f201])).
% 1.38/0.55  fof(f201,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | m1_subset_1(X0,sK1)) )),
% 1.38/0.55    inference(resolution,[],[f170,f88])).
% 1.38/0.55  fof(f88,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f31])).
% 1.38/0.55  fof(f31,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.38/0.55    inference(flattening,[],[f30])).
% 1.38/0.55  fof(f30,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.38/0.55    inference(ennf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.38/0.55  fof(f170,plain,(
% 1.38/0.55    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f166,f61])).
% 1.38/0.55  fof(f166,plain,(
% 1.38/0.55    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 1.38/0.55    inference(superposition,[],[f89,f99])).
% 1.38/0.55  fof(f89,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.55    inference(cnf_transformation,[],[f32])).
% 1.38/0.55  fof(f32,plain,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f11])).
% 1.38/0.55  fof(f11,axiom,(
% 1.38/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.38/0.55  fof(f179,plain,(
% 1.38/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0)) ) | ~spl11_7),
% 1.38/0.55    inference(avatar_component_clause,[],[f178])).
% 1.38/0.55  fof(f178,plain,(
% 1.38/0.55    spl11_7 <=> ! [X1,X2] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,sK1) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 1.38/0.55  fof(f387,plain,(
% 1.38/0.55    ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | (~spl11_8 | ~spl11_9)),
% 1.38/0.55    inference(subsumption_resolution,[],[f386,f237])).
% 1.38/0.55  fof(f237,plain,(
% 1.38/0.55    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~spl11_9),
% 1.38/0.55    inference(subsumption_resolution,[],[f234,f133])).
% 1.38/0.55  fof(f234,plain,(
% 1.38/0.55    v1_xboole_0(sK2) | r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~spl11_9),
% 1.38/0.55    inference(resolution,[],[f217,f106])).
% 1.38/0.55  fof(f217,plain,(
% 1.38/0.55    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | r2_hidden(sK5(X5,sK0,sK3,X6),X5)) ) | ~spl11_9),
% 1.38/0.55    inference(subsumption_resolution,[],[f191,f201])).
% 1.38/0.55  fof(f191,plain,(
% 1.38/0.55    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK5(X5,sK0,sK3,X6),X5)) ) | ~spl11_9),
% 1.38/0.55    inference(avatar_component_clause,[],[f190])).
% 1.38/0.55  fof(f190,plain,(
% 1.38/0.55    spl11_9 <=> ! [X5,X6] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | v1_xboole_0(X5) | ~m1_subset_1(X6,sK1) | r2_hidden(sK5(X5,sK0,sK3,X6),X5))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).
% 1.38/0.55  fof(f386,plain,(
% 1.38/0.55    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_8),
% 1.38/0.55    inference(trivial_inequality_removal,[],[f385])).
% 1.38/0.55  fof(f385,plain,(
% 1.38/0.55    sK4 != sK4 | ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl11_8),
% 1.38/0.55    inference(superposition,[],[f63,f300])).
% 1.38/0.55  fof(f300,plain,(
% 1.38/0.55    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~spl11_8),
% 1.38/0.55    inference(subsumption_resolution,[],[f299,f101])).
% 1.38/0.55  fof(f299,plain,(
% 1.38/0.55    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_relat_1(sK3) | ~spl11_8),
% 1.38/0.55    inference(subsumption_resolution,[],[f294,f60])).
% 1.38/0.55  fof(f60,plain,(
% 1.38/0.55    v1_funct_1(sK3)),
% 1.38/0.55    inference(cnf_transformation,[],[f38])).
% 1.38/0.55  fof(f294,plain,(
% 1.38/0.55    sK4 = k1_funct_1(sK3,sK5(sK2,sK0,sK3,sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl11_8),
% 1.38/0.55    inference(resolution,[],[f266,f86])).
% 1.38/0.55  fof(f86,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) = X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f59])).
% 1.38/0.55  fof(f59,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(flattening,[],[f58])).
% 1.38/0.55  fof(f58,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(nnf_transformation,[],[f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.38/0.55    inference(flattening,[],[f28])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.38/0.55    inference(ennf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.38/0.55  fof(f266,plain,(
% 1.38/0.55    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl11_8),
% 1.38/0.55    inference(subsumption_resolution,[],[f262,f133])).
% 1.38/0.55  fof(f262,plain,(
% 1.38/0.55    v1_xboole_0(sK2) | r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl11_8),
% 1.38/0.55    inference(resolution,[],[f218,f106])).
% 1.38/0.55  fof(f218,plain,(
% 1.38/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)) ) | ~spl11_8),
% 1.38/0.55    inference(subsumption_resolution,[],[f185,f201])).
% 1.38/0.55  fof(f185,plain,(
% 1.38/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3)) ) | ~spl11_8),
% 1.38/0.55    inference(avatar_component_clause,[],[f184])).
% 1.38/0.55  fof(f184,plain,(
% 1.38/0.55    spl11_8 <=> ! [X3,X4] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3) | ~m1_subset_1(X4,sK1) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_8])])).
% 1.38/0.55  fof(f63,plain,(
% 1.38/0.55    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f38])).
% 1.38/0.55  fof(f216,plain,(
% 1.38/0.55    spl11_4 | ~spl11_6),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f215])).
% 1.38/0.55  fof(f215,plain,(
% 1.38/0.55    $false | (spl11_4 | ~spl11_6)),
% 1.38/0.55    inference(subsumption_resolution,[],[f214,f176])).
% 1.38/0.55  fof(f214,plain,(
% 1.38/0.55    ~v1_xboole_0(sK0) | spl11_4),
% 1.38/0.55    inference(resolution,[],[f165,f68])).
% 1.38/0.55  fof(f165,plain,(
% 1.38/0.55    r2_hidden(sK7(sK0,k1_relat_1(sK3)),sK0) | spl11_4),
% 1.38/0.55    inference(resolution,[],[f149,f77])).
% 1.38/0.55  fof(f77,plain,(
% 1.38/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f53])).
% 1.38/0.55  fof(f53,plain,(
% 1.38/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 1.38/0.55  fof(f52,plain,(
% 1.38/0.55    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f51,plain,(
% 1.38/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.55    inference(rectify,[],[f50])).
% 1.38/0.55  fof(f50,plain,(
% 1.38/0.55    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.38/0.55    inference(nnf_transformation,[],[f24])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.55  fof(f149,plain,(
% 1.38/0.55    ~r1_tarski(sK0,k1_relat_1(sK3)) | spl11_4),
% 1.38/0.55    inference(avatar_component_clause,[],[f147])).
% 1.38/0.55  fof(f147,plain,(
% 1.38/0.55    spl11_4 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.38/0.55  fof(f197,plain,(
% 1.38/0.55    ~spl11_2),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f196])).
% 1.38/0.55  fof(f196,plain,(
% 1.38/0.55    $false | ~spl11_2),
% 1.38/0.55    inference(subsumption_resolution,[],[f114,f159])).
% 1.38/0.55  fof(f159,plain,(
% 1.38/0.55    ~v1_xboole_0(sK3)),
% 1.38/0.55    inference(resolution,[],[f127,f68])).
% 1.38/0.55  fof(f127,plain,(
% 1.38/0.55    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 1.38/0.55    inference(subsumption_resolution,[],[f123,f101])).
% 1.38/0.55  fof(f123,plain,(
% 1.38/0.55    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3)),
% 1.38/0.55    inference(resolution,[],[f106,f80])).
% 1.38/0.55  fof(f80,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f57])).
% 1.38/0.55  fof(f114,plain,(
% 1.38/0.55    v1_xboole_0(sK3) | ~spl11_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f112])).
% 1.38/0.55  fof(f112,plain,(
% 1.38/0.55    spl11_2 <=> v1_xboole_0(sK3)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.38/0.55  fof(f195,plain,(
% 1.38/0.55    spl11_1 | spl11_6 | spl11_7),
% 1.38/0.55    inference(avatar_split_clause,[],[f171,f178,f174,f108])).
% 1.38/0.55  fof(f108,plain,(
% 1.38/0.55    spl11_1 <=> v1_xboole_0(sK1)),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.38/0.55  fof(f171,plain,(
% 1.38/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f167,f61])).
% 1.38/0.55  fof(f167,plain,(
% 1.38/0.55    ( ! [X2,X1] : (~r2_hidden(X2,k9_relat_1(sK3,X1)) | m1_subset_1(sK5(X1,sK0,sK3,X2),sK0) | ~m1_subset_1(X2,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X1) | v1_xboole_0(sK1)) )),
% 1.38/0.55    inference(superposition,[],[f64,f99])).
% 1.38/0.55  fof(f64,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f42])).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.38/0.55  fof(f41,plain,(
% 1.38/0.55    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f40,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.38/0.55    inference(rectify,[],[f39])).
% 1.38/0.55  fof(f39,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.38/0.55    inference(nnf_transformation,[],[f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f14])).
% 1.38/0.55  fof(f14,axiom,(
% 1.38/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).
% 1.38/0.55  fof(f194,plain,(
% 1.38/0.55    spl11_1 | spl11_6 | spl11_8),
% 1.38/0.55    inference(avatar_split_clause,[],[f181,f184,f174,f108])).
% 1.38/0.55  fof(f181,plain,(
% 1.38/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f168,f61])).
% 1.38/0.55  fof(f168,plain,(
% 1.38/0.55    ( ! [X4,X3] : (~r2_hidden(X4,k9_relat_1(sK3,X3)) | r2_hidden(k4_tarski(sK5(X3,sK0,sK3,X4),X4),sK3) | ~m1_subset_1(X4,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X3) | v1_xboole_0(sK1)) )),
% 1.38/0.55    inference(superposition,[],[f65,f99])).
% 1.38/0.55  fof(f65,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f42])).
% 1.38/0.55  fof(f193,plain,(
% 1.38/0.55    spl11_1 | spl11_6 | spl11_9),
% 1.38/0.55    inference(avatar_split_clause,[],[f187,f190,f174,f108])).
% 1.38/0.55  fof(f187,plain,(
% 1.38/0.55    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 1.38/0.55    inference(subsumption_resolution,[],[f169,f61])).
% 1.38/0.55  fof(f169,plain,(
% 1.38/0.55    ( ! [X6,X5] : (~r2_hidden(X6,k9_relat_1(sK3,X5)) | r2_hidden(sK5(X5,sK0,sK3,X6),X5) | ~m1_subset_1(X6,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X5) | v1_xboole_0(sK1)) )),
% 1.38/0.55    inference(superposition,[],[f66,f99])).
% 1.38/0.55  fof(f66,plain,(
% 1.38/0.55    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | r2_hidden(sK5(X1,X2,X3,X4),X1) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f42])).
% 1.38/0.55  fof(f154,plain,(
% 1.38/0.55    ~spl11_4 | spl11_5),
% 1.38/0.55    inference(avatar_split_clause,[],[f145,f151,f147])).
% 1.38/0.55  fof(f145,plain,(
% 1.38/0.55    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3))),
% 1.38/0.55    inference(resolution,[],[f131,f75])).
% 1.38/0.55  fof(f75,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f49])).
% 1.38/0.55  fof(f49,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(flattening,[],[f48])).
% 1.38/0.55  fof(f48,plain,(
% 1.38/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.38/0.55    inference(nnf_transformation,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.55  fof(f131,plain,(
% 1.38/0.55    r1_tarski(k1_relat_1(sK3),sK0)),
% 1.38/0.55    inference(subsumption_resolution,[],[f130,f101])).
% 1.38/0.55  fof(f130,plain,(
% 1.38/0.55    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 1.38/0.55    inference(resolution,[],[f100,f70])).
% 1.38/0.55  fof(f70,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f47])).
% 1.38/0.55  fof(f47,plain,(
% 1.38/0.55    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.38/0.55    inference(nnf_transformation,[],[f22])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f5])).
% 1.38/0.55  fof(f5,axiom,(
% 1.38/0.55    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 1.38/0.55  fof(f100,plain,(
% 1.38/0.55    v4_relat_1(sK3,sK0)),
% 1.38/0.55    inference(resolution,[],[f61,f84])).
% 1.38/0.55  fof(f84,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f27])).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.55    inference(ennf_transformation,[],[f18])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.38/0.55    inference(pure_predicate_removal,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.38/0.55  fof(f115,plain,(
% 1.38/0.55    ~spl11_1 | spl11_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f102,f112,f108])).
% 1.38/0.55  fof(f102,plain,(
% 1.38/0.55    v1_xboole_0(sK3) | ~v1_xboole_0(sK1)),
% 1.38/0.55    inference(resolution,[],[f61,f72])).
% 1.38/0.55  fof(f72,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.38/0.55    inference(ennf_transformation,[],[f10])).
% 1.38/0.55  fof(f10,axiom,(
% 1.38/0.55    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.38/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (10450)------------------------------
% 1.38/0.55  % (10450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (10450)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (10450)Memory used [KB]: 10874
% 1.38/0.55  % (10450)Time elapsed: 0.109 s
% 1.38/0.55  % (10450)------------------------------
% 1.38/0.55  % (10450)------------------------------
% 1.38/0.56  % (10441)Success in time 0.194 s
%------------------------------------------------------------------------------
