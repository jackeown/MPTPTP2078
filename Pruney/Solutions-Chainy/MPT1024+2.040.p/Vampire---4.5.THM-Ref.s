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
% DateTime   : Thu Dec  3 13:06:17 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 733 expanded)
%              Number of leaves         :   23 ( 221 expanded)
%              Depth                    :   15
%              Number of atoms          :  479 (3807 expanded)
%              Number of equality atoms :   27 ( 548 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f123,f128,f146,f161,f234])).

fof(f234,plain,
    ( spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f233])).

fof(f233,plain,
    ( $false
    | spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f227,f222])).

fof(f222,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | spl10_2
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f113,f172,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f172,plain,
    ( m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_3 ),
    inference(unit_resulting_resolution,[],[f142,f100,f90,f117])).

fof(f117,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,sK1)
        | v1_xboole_0(X2)
        | ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) )
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl10_3
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,sK1)
        | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f90,plain,(
    r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f58,f88])).

fof(f88,plain,(
    ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(unit_resulting_resolution,[],[f57,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f38,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
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
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f58,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(unit_resulting_resolution,[],[f90,f91,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f87,f88])).

fof(f87,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f142,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f98,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
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

fof(f98,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f90,f89,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f89,plain,(
    v1_relat_1(sK3) ),
    inference(unit_resulting_resolution,[],[f67,f57,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f113,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl10_2
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f227,plain,
    ( ~ r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0)
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f173,f174,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(X0,sK2) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( sK4 != X1
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK3) ) ),
    inference(subsumption_resolution,[],[f94,f89])).

fof(f94,plain,(
    ! [X0,X1] :
      ( sK4 != X1
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sK4 != X1
      | ~ r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0)
      | ~ r2_hidden(k4_tarski(X0,X1),sK3)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f59,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f59,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f174,plain,
    ( r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3)
    | ~ spl10_4 ),
    inference(unit_resulting_resolution,[],[f142,f100,f90,f122])).

fof(f122,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,sK1)
        | v1_xboole_0(X4)
        | ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) )
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl10_4
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X5,sK1)
        | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f173,plain,
    ( r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2)
    | ~ spl10_5 ),
    inference(unit_resulting_resolution,[],[f142,f100,f90,f127])).

fof(f127,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X7,sK1)
        | v1_xboole_0(X6)
        | ~ r2_hidden(X7,k9_relat_1(sK3,X6))
        | r2_hidden(sK5(X6,sK0,sK3,X7),X6) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl10_5
  <=> ! [X7,X6] :
        ( ~ r2_hidden(X7,k9_relat_1(sK3,X6))
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X7,sK1)
        | r2_hidden(sK5(X6,sK0,sK3,X7),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f161,plain,(
    ~ spl10_1 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f159,f149])).

fof(f149,plain,
    ( v1_xboole_0(sK3)
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f57,f110,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f110,plain,
    ( v1_xboole_0(sK1)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl10_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f159,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(unit_resulting_resolution,[],[f97,f65])).

fof(f97,plain,(
    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    inference(unit_resulting_resolution,[],[f90,f89,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f146,plain,(
    ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f143,f141])).

fof(f141,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f136,f65])).

fof(f136,plain,
    ( v1_xboole_0(sK3)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f57,f114,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f114,plain,
    ( v1_xboole_0(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f143,plain,(
    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),k1_funct_1(sK3,sK8(sK4,sK2,sK3))),sK3) ),
    inference(unit_resulting_resolution,[],[f89,f56,f96,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    inference(unit_resulting_resolution,[],[f90,f89,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f128,plain,
    ( spl10_1
    | spl10_2
    | spl10_5 ),
    inference(avatar_split_clause,[],[f124,f126,f112,f108])).

fof(f124,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k9_relat_1(sK3,X6))
      | r2_hidden(sK5(X6,sK0,sK3,X7),X6)
      | ~ m1_subset_1(X7,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X6)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f104,f57])).

fof(f104,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k9_relat_1(sK3,X6))
      | r2_hidden(sK5(X6,sK0,sK3,X7),X6)
      | ~ m1_subset_1(X7,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X6)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f62,f88])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK5(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).

fof(f42,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK5(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK5(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

fof(f123,plain,
    ( spl10_1
    | spl10_2
    | spl10_4 ),
    inference(avatar_split_clause,[],[f119,f121,f112,f108])).

fof(f119,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3)
      | ~ m1_subset_1(X5,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f103,f57])).

fof(f103,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,k9_relat_1(sK3,X4))
      | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3)
      | ~ m1_subset_1(X5,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f61,f88])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f118,plain,
    ( spl10_1
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f106,f116,f112,f108])).

fof(f106,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0)
      | ~ m1_subset_1(X3,sK1)
      | v1_xboole_0(sK0)
      | v1_xboole_0(X2)
      | v1_xboole_0(sK1) ) ),
    inference(subsumption_resolution,[],[f102,f57])).

fof(f102,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k9_relat_1(sK3,X2))
      | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0)
      | ~ m1_subset_1(X3,sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | v1_xboole_0(sK0)
      | v1_xboole_0(X2)
      | v1_xboole_0(sK1) ) ),
    inference(superposition,[],[f60,f88])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:18:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (9734)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (9743)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.51  % (9740)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.51  % (9735)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (9741)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (9736)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (9737)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (9751)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.53  % (9744)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.54  % (9746)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (9745)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.54  % (9736)Refutation not found, incomplete strategy% (9736)------------------------------
% 1.29/0.54  % (9736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (9736)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (9736)Memory used [KB]: 10746
% 1.29/0.54  % (9736)Time elapsed: 0.110 s
% 1.29/0.54  % (9736)------------------------------
% 1.29/0.54  % (9736)------------------------------
% 1.29/0.54  % (9762)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.54  % (9756)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.54  % (9754)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.54  % (9760)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (9748)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.55  % (9747)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.55  % (9753)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.43/0.55  % (9752)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.43/0.55  % (9738)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.43/0.55  % (9744)Refutation not found, incomplete strategy% (9744)------------------------------
% 1.43/0.55  % (9744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (9744)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (9744)Memory used [KB]: 10618
% 1.43/0.55  % (9744)Time elapsed: 0.147 s
% 1.43/0.55  % (9744)------------------------------
% 1.43/0.55  % (9744)------------------------------
% 1.43/0.56  % (9763)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.56  % (9756)Refutation not found, incomplete strategy% (9756)------------------------------
% 1.43/0.56  % (9756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (9756)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (9756)Memory used [KB]: 10874
% 1.43/0.56  % (9756)Time elapsed: 0.129 s
% 1.43/0.56  % (9756)------------------------------
% 1.43/0.56  % (9756)------------------------------
% 1.43/0.56  % (9745)Refutation not found, incomplete strategy% (9745)------------------------------
% 1.43/0.56  % (9745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (9745)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (9745)Memory used [KB]: 10618
% 1.43/0.56  % (9745)Time elapsed: 0.152 s
% 1.43/0.56  % (9745)------------------------------
% 1.43/0.56  % (9745)------------------------------
% 1.43/0.56  % (9757)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.43/0.56  % (9755)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.56  % (9749)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.43/0.56  % (9761)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.57  % (9742)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.57  % (9758)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.43/0.57  % (9759)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.43/0.57  % (9760)Refutation found. Thanks to Tanya!
% 1.43/0.57  % SZS status Theorem for theBenchmark
% 1.43/0.57  % SZS output start Proof for theBenchmark
% 1.43/0.57  fof(f235,plain,(
% 1.43/0.57    $false),
% 1.43/0.57    inference(avatar_sat_refutation,[],[f118,f123,f128,f146,f161,f234])).
% 1.43/0.57  fof(f234,plain,(
% 1.43/0.57    spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f233])).
% 1.43/0.57  fof(f233,plain,(
% 1.43/0.57    $false | (spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5)),
% 1.43/0.57    inference(subsumption_resolution,[],[f227,f222])).
% 1.43/0.57  fof(f222,plain,(
% 1.43/0.57    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | (spl10_2 | ~spl10_3)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f113,f172,f70])).
% 1.43/0.57  fof(f70,plain,(
% 1.43/0.57    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f26])).
% 1.43/0.57  fof(f26,plain,(
% 1.43/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.43/0.57    inference(flattening,[],[f25])).
% 1.43/0.57  fof(f25,plain,(
% 1.43/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.43/0.57    inference(ennf_transformation,[],[f3])).
% 1.43/0.57  fof(f3,axiom,(
% 1.43/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 1.43/0.57  fof(f172,plain,(
% 1.43/0.57    m1_subset_1(sK5(sK2,sK0,sK3,sK4),sK0) | ~spl10_3),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f142,f100,f90,f117])).
% 1.43/0.57  fof(f117,plain,(
% 1.43/0.57    ( ! [X2,X3] : (~m1_subset_1(X3,sK1) | v1_xboole_0(X2) | ~r2_hidden(X3,k9_relat_1(sK3,X2)) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0)) ) | ~spl10_3),
% 1.43/0.57    inference(avatar_component_clause,[],[f116])).
% 1.43/0.57  fof(f116,plain,(
% 1.43/0.57    spl10_3 <=> ! [X3,X2] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | v1_xboole_0(X2) | ~m1_subset_1(X3,sK1) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.43/0.57  fof(f90,plain,(
% 1.43/0.57    r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.43/0.57    inference(backward_demodulation,[],[f58,f88])).
% 1.43/0.57  fof(f88,plain,(
% 1.43/0.57    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) )),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f57,f82])).
% 1.43/0.57  fof(f82,plain,(
% 1.43/0.57    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f34])).
% 1.43/0.57  fof(f34,plain,(
% 1.43/0.57    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.57    inference(ennf_transformation,[],[f12])).
% 1.43/0.57  fof(f12,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.43/0.57  fof(f57,plain,(
% 1.43/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.43/0.57    inference(cnf_transformation,[],[f39])).
% 1.43/0.57  fof(f39,plain,(
% 1.43/0.57    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3)),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f20,f38,f37])).
% 1.43/0.57  fof(f37,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK3))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f38,plain,(
% 1.43/0.57    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f20,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 1.43/0.57    inference(flattening,[],[f19])).
% 1.43/0.57  fof(f19,plain,(
% 1.43/0.57    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 1.43/0.57    inference(ennf_transformation,[],[f18])).
% 1.43/0.57  fof(f18,plain,(
% 1.43/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.43/0.57    inference(pure_predicate_removal,[],[f16])).
% 1.43/0.57  fof(f16,negated_conjecture,(
% 1.43/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.43/0.57    inference(negated_conjecture,[],[f15])).
% 1.43/0.57  fof(f15,conjecture,(
% 1.43/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).
% 1.43/0.57  fof(f58,plain,(
% 1.43/0.57    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.43/0.57    inference(cnf_transformation,[],[f39])).
% 1.43/0.57  fof(f100,plain,(
% 1.43/0.57    m1_subset_1(sK4,sK1)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f90,f91,f80])).
% 1.43/0.57  fof(f80,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f32])).
% 1.43/0.57  fof(f32,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.43/0.57    inference(flattening,[],[f31])).
% 1.43/0.57  fof(f31,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.43/0.57    inference(ennf_transformation,[],[f4])).
% 1.43/0.57  fof(f4,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 1.43/0.57  fof(f91,plain,(
% 1.43/0.57    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.43/0.57    inference(forward_demodulation,[],[f87,f88])).
% 1.43/0.57  fof(f87,plain,(
% 1.43/0.57    ( ! [X0] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X0),k1_zfmisc_1(sK1))) )),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f57,f81])).
% 1.43/0.57  fof(f81,plain,(
% 1.43/0.57    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f33])).
% 1.43/0.57  fof(f33,plain,(
% 1.43/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.43/0.57    inference(ennf_transformation,[],[f11])).
% 1.43/0.57  fof(f11,axiom,(
% 1.43/0.57    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.43/0.57  fof(f142,plain,(
% 1.43/0.57    ~v1_xboole_0(sK2)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f98,f65])).
% 1.43/0.57  fof(f65,plain,(
% 1.43/0.57    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f47])).
% 1.43/0.57  fof(f47,plain,(
% 1.43/0.57    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f45,f46])).
% 1.43/0.57  fof(f46,plain,(
% 1.43/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f45,plain,(
% 1.43/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.43/0.57    inference(rectify,[],[f44])).
% 1.43/0.57  fof(f44,plain,(
% 1.43/0.57    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.43/0.57    inference(nnf_transformation,[],[f1])).
% 1.43/0.57  fof(f1,axiom,(
% 1.43/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.43/0.57  fof(f98,plain,(
% 1.43/0.57    r2_hidden(sK8(sK4,sK2,sK3),sK2)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f90,f89,f75])).
% 1.43/0.57  fof(f75,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f53])).
% 1.43/0.57  fof(f53,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f51,f52])).
% 1.43/0.57  fof(f52,plain,(
% 1.43/0.57    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f51,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(rectify,[],[f50])).
% 1.43/0.57  fof(f50,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(nnf_transformation,[],[f28])).
% 1.43/0.57  fof(f28,plain,(
% 1.43/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(ennf_transformation,[],[f7])).
% 1.43/0.57  fof(f7,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.43/0.57  fof(f89,plain,(
% 1.43/0.57    v1_relat_1(sK3)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f67,f57,f64])).
% 1.43/0.57  fof(f64,plain,(
% 1.43/0.57    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f22])).
% 1.43/0.57  fof(f22,plain,(
% 1.43/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.43/0.57    inference(ennf_transformation,[],[f5])).
% 1.43/0.57  fof(f5,axiom,(
% 1.43/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.43/0.57  fof(f67,plain,(
% 1.43/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.43/0.57    inference(cnf_transformation,[],[f6])).
% 1.43/0.57  fof(f6,axiom,(
% 1.43/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.43/0.57  fof(f113,plain,(
% 1.43/0.57    ~v1_xboole_0(sK0) | spl10_2),
% 1.43/0.57    inference(avatar_component_clause,[],[f112])).
% 1.43/0.57  fof(f112,plain,(
% 1.43/0.57    spl10_2 <=> v1_xboole_0(sK0)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.43/0.57  fof(f227,plain,(
% 1.43/0.57    ~r2_hidden(sK5(sK2,sK0,sK3,sK4),sK0) | (~spl10_4 | ~spl10_5)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f173,f174,f134])).
% 1.43/0.57  fof(f134,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK0) | ~r2_hidden(X0,sK2)) )),
% 1.43/0.57    inference(equality_resolution,[],[f95])).
% 1.43/0.57  fof(f95,plain,(
% 1.43/0.57    ( ! [X0,X1] : (sK4 != X1 | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3)) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f94,f89])).
% 1.43/0.57  fof(f94,plain,(
% 1.43/0.57    ( ! [X0,X1] : (sK4 != X1 | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3) | ~v1_relat_1(sK3)) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f93,f56])).
% 1.43/0.57  fof(f56,plain,(
% 1.43/0.57    v1_funct_1(sK3)),
% 1.43/0.57    inference(cnf_transformation,[],[f39])).
% 1.43/0.57  fof(f93,plain,(
% 1.43/0.57    ( ! [X0,X1] : (sK4 != X1 | ~r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | ~r2_hidden(k4_tarski(X0,X1),sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.43/0.57    inference(superposition,[],[f59,f78])).
% 1.43/0.57  fof(f78,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f55])).
% 1.43/0.57  fof(f55,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(flattening,[],[f54])).
% 1.43/0.57  fof(f54,plain,(
% 1.43/0.57    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(nnf_transformation,[],[f30])).
% 1.43/0.57  fof(f30,plain,(
% 1.43/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.43/0.57    inference(flattening,[],[f29])).
% 1.43/0.57  fof(f29,plain,(
% 1.43/0.57    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.43/0.57    inference(ennf_transformation,[],[f8])).
% 1.43/0.57  fof(f8,axiom,(
% 1.43/0.57    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 1.43/0.57  fof(f59,plain,(
% 1.43/0.57    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f39])).
% 1.43/0.57  fof(f174,plain,(
% 1.43/0.57    r2_hidden(k4_tarski(sK5(sK2,sK0,sK3,sK4),sK4),sK3) | ~spl10_4),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f142,f100,f90,f122])).
% 1.43/0.57  fof(f122,plain,(
% 1.43/0.57    ( ! [X4,X5] : (~m1_subset_1(X5,sK1) | v1_xboole_0(X4) | ~r2_hidden(X5,k9_relat_1(sK3,X4)) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3)) ) | ~spl10_4),
% 1.43/0.57    inference(avatar_component_clause,[],[f121])).
% 1.43/0.57  fof(f121,plain,(
% 1.43/0.57    spl10_4 <=> ! [X5,X4] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | v1_xboole_0(X4) | ~m1_subset_1(X5,sK1) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.43/0.57  fof(f173,plain,(
% 1.43/0.57    r2_hidden(sK5(sK2,sK0,sK3,sK4),sK2) | ~spl10_5),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f142,f100,f90,f127])).
% 1.43/0.57  fof(f127,plain,(
% 1.43/0.57    ( ! [X6,X7] : (~m1_subset_1(X7,sK1) | v1_xboole_0(X6) | ~r2_hidden(X7,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X6,sK0,sK3,X7),X6)) ) | ~spl10_5),
% 1.43/0.57    inference(avatar_component_clause,[],[f126])).
% 1.43/0.57  fof(f126,plain,(
% 1.43/0.57    spl10_5 <=> ! [X7,X6] : (~r2_hidden(X7,k9_relat_1(sK3,X6)) | v1_xboole_0(X6) | ~m1_subset_1(X7,sK1) | r2_hidden(sK5(X6,sK0,sK3,X7),X6))),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.43/0.57  fof(f161,plain,(
% 1.43/0.57    ~spl10_1),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f160])).
% 1.43/0.57  fof(f160,plain,(
% 1.43/0.57    $false | ~spl10_1),
% 1.43/0.57    inference(subsumption_resolution,[],[f159,f149])).
% 1.43/0.57  fof(f149,plain,(
% 1.43/0.57    v1_xboole_0(sK3) | ~spl10_1),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f57,f110,f68])).
% 1.43/0.57  fof(f68,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f23])).
% 1.43/0.57  fof(f23,plain,(
% 1.43/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.43/0.57    inference(ennf_transformation,[],[f10])).
% 1.43/0.57  fof(f10,axiom,(
% 1.43/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.43/0.57  fof(f110,plain,(
% 1.43/0.57    v1_xboole_0(sK1) | ~spl10_1),
% 1.43/0.57    inference(avatar_component_clause,[],[f108])).
% 1.43/0.57  fof(f108,plain,(
% 1.43/0.57    spl10_1 <=> v1_xboole_0(sK1)),
% 1.43/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.43/0.57  fof(f159,plain,(
% 1.43/0.57    ~v1_xboole_0(sK3)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f97,f65])).
% 1.43/0.57  fof(f97,plain,(
% 1.43/0.57    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f90,f89,f74])).
% 1.43/0.57  fof(f74,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f53])).
% 1.43/0.57  fof(f146,plain,(
% 1.43/0.57    ~spl10_2),
% 1.43/0.57    inference(avatar_contradiction_clause,[],[f145])).
% 1.43/0.57  fof(f145,plain,(
% 1.43/0.57    $false | ~spl10_2),
% 1.43/0.57    inference(subsumption_resolution,[],[f143,f141])).
% 1.43/0.57  fof(f141,plain,(
% 1.43/0.57    ( ! [X0] : (~r2_hidden(X0,sK3)) ) | ~spl10_2),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f136,f65])).
% 1.43/0.57  fof(f136,plain,(
% 1.43/0.57    v1_xboole_0(sK3) | ~spl10_2),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f57,f114,f69])).
% 1.43/0.57  fof(f69,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f24])).
% 1.43/0.57  fof(f24,plain,(
% 1.43/0.57    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.43/0.57    inference(ennf_transformation,[],[f9])).
% 1.43/0.57  fof(f9,axiom,(
% 1.43/0.57    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.43/0.57  fof(f114,plain,(
% 1.43/0.57    v1_xboole_0(sK0) | ~spl10_2),
% 1.43/0.57    inference(avatar_component_clause,[],[f112])).
% 1.43/0.57  fof(f143,plain,(
% 1.43/0.57    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),k1_funct_1(sK3,sK8(sK4,sK2,sK3))),sK3)),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f89,f56,f96,f84])).
% 1.43/0.57  fof(f84,plain,(
% 1.43/0.57    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.43/0.57    inference(equality_resolution,[],[f79])).
% 1.43/0.57  fof(f79,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f55])).
% 1.43/0.57  fof(f96,plain,(
% 1.43/0.57    r2_hidden(sK8(sK4,sK2,sK3),k1_relat_1(sK3))),
% 1.43/0.57    inference(unit_resulting_resolution,[],[f90,f89,f73])).
% 1.43/0.57  fof(f73,plain,(
% 1.43/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f53])).
% 1.43/0.57  fof(f128,plain,(
% 1.43/0.57    spl10_1 | spl10_2 | spl10_5),
% 1.43/0.57    inference(avatar_split_clause,[],[f124,f126,f112,f108])).
% 1.43/0.57  fof(f124,plain,(
% 1.43/0.57    ( ! [X6,X7] : (~r2_hidden(X7,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X6,sK0,sK3,X7),X6) | ~m1_subset_1(X7,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X6) | v1_xboole_0(sK1)) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f104,f57])).
% 1.43/0.57  fof(f104,plain,(
% 1.43/0.57    ( ! [X6,X7] : (~r2_hidden(X7,k9_relat_1(sK3,X6)) | r2_hidden(sK5(X6,sK0,sK3,X7),X6) | ~m1_subset_1(X7,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X6) | v1_xboole_0(sK1)) )),
% 1.43/0.57    inference(superposition,[],[f62,f88])).
% 1.43/0.57  fof(f62,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK5(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f43])).
% 1.43/0.57  fof(f43,plain,(
% 1.43/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.43/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f41,f42])).
% 1.43/0.57  fof(f42,plain,(
% 1.43/0.57    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK5(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK5(X1,X2,X3,X4),X2)))),
% 1.43/0.57    introduced(choice_axiom,[])).
% 1.43/0.57  fof(f41,plain,(
% 1.43/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.43/0.57    inference(rectify,[],[f40])).
% 1.43/0.57  fof(f40,plain,(
% 1.43/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.43/0.57    inference(nnf_transformation,[],[f21])).
% 1.43/0.57  fof(f21,plain,(
% 1.43/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.43/0.57    inference(ennf_transformation,[],[f14])).
% 1.43/0.57  fof(f14,axiom,(
% 1.43/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 1.43/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 1.43/0.57  fof(f123,plain,(
% 1.43/0.57    spl10_1 | spl10_2 | spl10_4),
% 1.43/0.57    inference(avatar_split_clause,[],[f119,f121,f112,f108])).
% 1.43/0.57  fof(f119,plain,(
% 1.43/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) | ~m1_subset_1(X5,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X4) | v1_xboole_0(sK1)) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f103,f57])).
% 1.43/0.57  fof(f103,plain,(
% 1.43/0.57    ( ! [X4,X5] : (~r2_hidden(X5,k9_relat_1(sK3,X4)) | r2_hidden(k4_tarski(sK5(X4,sK0,sK3,X5),X5),sK3) | ~m1_subset_1(X5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X4) | v1_xboole_0(sK1)) )),
% 1.43/0.57    inference(superposition,[],[f61,f88])).
% 1.43/0.57  fof(f61,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f43])).
% 1.43/0.57  fof(f118,plain,(
% 1.43/0.57    spl10_1 | spl10_2 | spl10_3),
% 1.43/0.57    inference(avatar_split_clause,[],[f106,f116,f112,f108])).
% 1.43/0.57  fof(f106,plain,(
% 1.43/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) | ~m1_subset_1(X3,sK1) | v1_xboole_0(sK0) | v1_xboole_0(X2) | v1_xboole_0(sK1)) )),
% 1.43/0.57    inference(subsumption_resolution,[],[f102,f57])).
% 1.43/0.57  fof(f102,plain,(
% 1.43/0.57    ( ! [X2,X3] : (~r2_hidden(X3,k9_relat_1(sK3,X2)) | m1_subset_1(sK5(X2,sK0,sK3,X3),sK0) | ~m1_subset_1(X3,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | v1_xboole_0(sK0) | v1_xboole_0(X2) | v1_xboole_0(sK1)) )),
% 1.43/0.57    inference(superposition,[],[f60,f88])).
% 1.43/0.57  fof(f60,plain,(
% 1.43/0.57    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.43/0.57    inference(cnf_transformation,[],[f43])).
% 1.43/0.57  % SZS output end Proof for theBenchmark
% 1.43/0.57  % (9760)------------------------------
% 1.43/0.57  % (9760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (9760)Termination reason: Refutation
% 1.43/0.57  
% 1.43/0.57  % (9760)Memory used [KB]: 11001
% 1.43/0.57  % (9760)Time elapsed: 0.148 s
% 1.43/0.57  % (9760)------------------------------
% 1.43/0.57  % (9760)------------------------------
% 1.43/0.57  % (9733)Success in time 0.203 s
%------------------------------------------------------------------------------
