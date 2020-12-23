%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:38 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 380 expanded)
%              Number of leaves         :   41 ( 139 expanded)
%              Depth                    :   17
%              Number of atoms          :  553 (1662 expanded)
%              Number of equality atoms :   54 (  92 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f882,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f209,f211,f295,f297,f299,f301,f303,f518,f530,f532,f588,f647,f716,f727,f741,f759,f764,f881])).

fof(f881,plain,
    ( spl5_1
    | ~ spl5_17 ),
    inference(avatar_contradiction_clause,[],[f880])).

fof(f880,plain,
    ( $false
    | spl5_1
    | ~ spl5_17 ),
    inference(resolution,[],[f860,f117])).

fof(f117,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f98,f96])).

fof(f96,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f65,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f71,f67])).

fof(f71,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f860,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl5_1
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f109,f851])).

fof(f851,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_17 ),
    inference(resolution,[],[f833,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f124,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f124,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f123,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f123,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f122,f115])).

fof(f115,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f68,f66])).

fof(f66,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f89,f64])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f833,plain,
    ( ! [X4] : r1_tarski(sK2,X4)
    | ~ spl5_17 ),
    inference(resolution,[],[f780,f351])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f348,f118])).

fof(f118,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(superposition,[],[f97,f96])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f348,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X3) ) ),
    inference(resolution,[],[f344,f64])).

fof(f344,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | r1_tarski(X1,X4) ) ),
    inference(resolution,[],[f127,f82])).

fof(f127,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X4,X3)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f74,f89])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f780,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f766,f367])).

fof(f367,plain,(
    ! [X12] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X12) ),
    inference(resolution,[],[f360,f126])).

fof(f360,plain,(
    ! [X8,X9] : r1_tarski(k2_zfmisc_1(k1_xboole_0,X8),X9) ),
    inference(resolution,[],[f354,f115])).

fof(f354,plain,(
    ! [X12,X13,X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12)))
      | r1_tarski(X11,X13) ) ),
    inference(resolution,[],[f348,f115])).

fof(f766,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_17 ),
    inference(backward_demodulation,[],[f58,f499])).

fof(f499,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl5_17
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f109,plain,
    ( ~ v2_funct_1(sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f764,plain,
    ( ~ spl5_8
    | ~ spl5_15
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_16
    | ~ spl5_11
    | spl5_1
    | spl5_17
    | ~ spl5_18
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f637,f206,f501,f497,f107,f292,f493,f288,f284,f489,f280])).

fof(f280,plain,
    ( spl5_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f489,plain,
    ( spl5_15
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f284,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f288,plain,
    ( spl5_10
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f493,plain,
    ( spl5_16
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f292,plain,
    ( spl5_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f501,plain,
    ( spl5_18
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f206,plain,
    ( spl5_5
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f637,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl5_5 ),
    inference(superposition,[],[f90,f208])).

fof(f208,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f759,plain,
    ( ~ spl5_21
    | ~ spl5_32
    | spl5_2
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f756,f662,f111,f691,f552])).

fof(f552,plain,
    ( spl5_21
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f691,plain,
    ( spl5_32
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f111,plain,
    ( spl5_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f662,plain,
    ( spl5_29
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f756,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl5_29 ),
    inference(superposition,[],[f100,f663])).

fof(f663,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f662])).

fof(f100,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f741,plain,
    ( ~ spl5_11
    | spl5_29
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f739,f640,f662,f292])).

fof(f640,plain,
    ( spl5_25
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f739,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_25 ),
    inference(superposition,[],[f85,f642])).

fof(f642,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f640])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f727,plain,
    ( ~ spl5_5
    | spl5_26 ),
    inference(avatar_contradiction_clause,[],[f725])).

fof(f725,plain,
    ( $false
    | ~ spl5_5
    | spl5_26 ),
    inference(resolution,[],[f646,f304])).

fof(f304,plain,
    ( r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | ~ spl5_5 ),
    inference(backward_demodulation,[],[f62,f208])).

fof(f62,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f646,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | spl5_26 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl5_26
  <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f716,plain,(
    spl5_32 ),
    inference(avatar_contradiction_clause,[],[f714])).

fof(f714,plain,
    ( $false
    | spl5_32 ),
    inference(resolution,[],[f695,f61])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f695,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl5_32 ),
    inference(resolution,[],[f693,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f693,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl5_32 ),
    inference(avatar_component_clause,[],[f691])).

fof(f647,plain,
    ( ~ spl5_10
    | ~ spl5_16
    | ~ spl5_11
    | ~ spl5_8
    | ~ spl5_15
    | ~ spl5_9
    | spl5_25
    | ~ spl5_26
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f638,f206,f644,f640,f284,f489,f280,f292,f493,f288])).

fof(f638,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl5_5 ),
    inference(superposition,[],[f88,f208])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f588,plain,(
    spl5_21 ),
    inference(avatar_contradiction_clause,[],[f585])).

fof(f585,plain,
    ( $false
    | spl5_21 ),
    inference(resolution,[],[f560,f61])).

fof(f560,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl5_21 ),
    inference(resolution,[],[f554,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f554,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_21 ),
    inference(avatar_component_clause,[],[f552])).

fof(f532,plain,(
    spl5_16 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | spl5_16 ),
    inference(resolution,[],[f495,f60])).

fof(f60,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f495,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f493])).

fof(f530,plain,(
    spl5_15 ),
    inference(avatar_contradiction_clause,[],[f529])).

fof(f529,plain,
    ( $false
    | spl5_15 ),
    inference(resolution,[],[f491,f57])).

fof(f57,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f491,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f489])).

fof(f518,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f503,f98])).

fof(f503,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f501])).

fof(f303,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f294,f61])).

fof(f294,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f292])).

fof(f301,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f286,f58])).

fof(f286,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f284])).

fof(f299,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f290,f59])).

fof(f59,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f290,plain,
    ( ~ v1_funct_1(sK3)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f288])).

fof(f297,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f282,f56])).

fof(f56,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f282,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f280])).

fof(f295,plain,
    ( ~ spl5_8
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_11
    | spl5_3 ),
    inference(avatar_split_clause,[],[f278,f198,f292,f288,f284,f280])).

fof(f198,plain,
    ( spl5_3
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f278,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_3 ),
    inference(resolution,[],[f95,f200])).

fof(f200,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f198])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f211,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f204,f97])).

fof(f204,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f202])).

fof(f202,plain,
    ( spl5_4
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f209,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f194,f206,f202,f198])).

fof(f194,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f92,f62])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f114,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f63,f111,f107])).

fof(f63,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (27382)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (27375)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (27390)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (27392)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (27384)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (27377)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (27395)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (27374)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (27373)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (27372)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (27378)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (27399)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (27376)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (27398)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (27379)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (27391)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (27387)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (27393)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (27392)Refutation not found, incomplete strategy% (27392)------------------------------
% 0.21/0.55  % (27392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27392)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27392)Memory used [KB]: 10874
% 0.21/0.55  % (27392)Time elapsed: 0.070 s
% 0.21/0.55  % (27392)------------------------------
% 0.21/0.55  % (27392)------------------------------
% 0.21/0.55  % (27380)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (27383)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (27397)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (27371)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.56  % (27370)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.56  % (27386)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.51/0.56  % (27388)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.51/0.56  % (27389)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.51/0.56  % (27385)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.51/0.57  % (27396)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.51/0.57  % (27381)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.62/0.58  % (27382)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  fof(f882,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(avatar_sat_refutation,[],[f114,f209,f211,f295,f297,f299,f301,f303,f518,f530,f532,f588,f647,f716,f727,f741,f759,f764,f881])).
% 1.62/0.58  fof(f881,plain,(
% 1.62/0.58    spl5_1 | ~spl5_17),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f880])).
% 1.62/0.58  fof(f880,plain,(
% 1.62/0.58    $false | (spl5_1 | ~spl5_17)),
% 1.62/0.58    inference(resolution,[],[f860,f117])).
% 1.62/0.58  fof(f117,plain,(
% 1.62/0.58    v2_funct_1(k1_xboole_0)),
% 1.62/0.58    inference(superposition,[],[f98,f96])).
% 1.62/0.58  fof(f96,plain,(
% 1.62/0.58    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.62/0.58    inference(definition_unfolding,[],[f65,f67])).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f19])).
% 1.62/0.58  fof(f19,axiom,(
% 1.62/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.62/0.58    inference(cnf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.62/0.58  fof(f98,plain,(
% 1.62/0.58    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f71,f67])).
% 1.62/0.58  fof(f71,plain,(
% 1.62/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.62/0.58  fof(f860,plain,(
% 1.62/0.58    ~v2_funct_1(k1_xboole_0) | (spl5_1 | ~spl5_17)),
% 1.62/0.58    inference(backward_demodulation,[],[f109,f851])).
% 1.62/0.58  fof(f851,plain,(
% 1.62/0.58    k1_xboole_0 = sK2 | ~spl5_17),
% 1.62/0.58    inference(resolution,[],[f833,f126])).
% 1.62/0.58  fof(f126,plain,(
% 1.62/0.58    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.62/0.58    inference(resolution,[],[f124,f80])).
% 1.62/0.58  fof(f80,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f50])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.58    inference(flattening,[],[f49])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.62/0.58    inference(nnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.62/0.58  fof(f124,plain,(
% 1.62/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.58    inference(resolution,[],[f123,f82])).
% 1.62/0.58  fof(f82,plain,(
% 1.62/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.58    inference(rectify,[],[f51])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.62/0.58    inference(nnf_transformation,[],[f31])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.58  fof(f123,plain,(
% 1.62/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.58    inference(resolution,[],[f122,f115])).
% 1.62/0.58  fof(f115,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f68,f66])).
% 1.62/0.58  fof(f66,plain,(
% 1.62/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.62/0.58  fof(f68,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.62/0.58  fof(f122,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~r2_hidden(X1,X0)) )),
% 1.62/0.58    inference(resolution,[],[f89,f64])).
% 1.62/0.58  fof(f64,plain,(
% 1.62/0.58    v1_xboole_0(k1_xboole_0)),
% 1.62/0.58    inference(cnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    v1_xboole_0(k1_xboole_0)),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.62/0.58  fof(f89,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f37])).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.62/0.58    inference(ennf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.62/0.58  fof(f833,plain,(
% 1.62/0.58    ( ! [X4] : (r1_tarski(sK2,X4)) ) | ~spl5_17),
% 1.62/0.58    inference(resolution,[],[f780,f351])).
% 1.62/0.58  fof(f351,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(resolution,[],[f348,f118])).
% 1.62/0.58  fof(f118,plain,(
% 1.62/0.58    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.62/0.58    inference(superposition,[],[f97,f96])).
% 1.62/0.58  fof(f97,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f69,f67])).
% 1.62/0.58  fof(f69,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,axiom,(
% 1.62/0.58    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.62/0.58  fof(f348,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X3)) )),
% 1.62/0.58    inference(resolution,[],[f344,f64])).
% 1.62/0.58  fof(f344,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | r1_tarski(X1,X4)) )),
% 1.62/0.58    inference(resolution,[],[f127,f82])).
% 1.62/0.58  fof(f127,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X4,X3) | ~v1_xboole_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.62/0.58    inference(resolution,[],[f74,f89])).
% 1.62/0.58  fof(f74,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f27])).
% 1.62/0.58  fof(f27,plain,(
% 1.62/0.58    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,axiom,(
% 1.62/0.58    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.62/0.58  fof(f780,plain,(
% 1.62/0.58    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_17),
% 1.62/0.58    inference(forward_demodulation,[],[f766,f367])).
% 1.62/0.58  fof(f367,plain,(
% 1.62/0.58    ( ! [X12] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X12)) )),
% 1.62/0.58    inference(resolution,[],[f360,f126])).
% 1.62/0.58  fof(f360,plain,(
% 1.62/0.58    ( ! [X8,X9] : (r1_tarski(k2_zfmisc_1(k1_xboole_0,X8),X9)) )),
% 1.62/0.58    inference(resolution,[],[f354,f115])).
% 1.62/0.58  fof(f354,plain,(
% 1.62/0.58    ( ! [X12,X13,X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X12))) | r1_tarski(X11,X13)) )),
% 1.62/0.58    inference(resolution,[],[f348,f115])).
% 1.62/0.58  fof(f766,plain,(
% 1.62/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl5_17),
% 1.62/0.58    inference(backward_demodulation,[],[f58,f499])).
% 1.62/0.58  fof(f499,plain,(
% 1.62/0.58    k1_xboole_0 = sK0 | ~spl5_17),
% 1.62/0.58    inference(avatar_component_clause,[],[f497])).
% 1.62/0.58  fof(f497,plain,(
% 1.62/0.58    spl5_17 <=> k1_xboole_0 = sK0),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.62/0.58  fof(f58,plain,(
% 1.62/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f45,f44])).
% 1.62/0.58  fof(f44,plain,(
% 1.62/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f45,plain,(
% 1.62/0.58    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f25,plain,(
% 1.62/0.58    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.62/0.58    inference(flattening,[],[f24])).
% 1.62/0.58  fof(f24,plain,(
% 1.62/0.58    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.62/0.58    inference(ennf_transformation,[],[f23])).
% 1.62/0.58  fof(f23,negated_conjecture,(
% 1.62/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.62/0.58    inference(negated_conjecture,[],[f22])).
% 1.62/0.58  fof(f22,conjecture,(
% 1.62/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.62/0.58  fof(f109,plain,(
% 1.62/0.58    ~v2_funct_1(sK2) | spl5_1),
% 1.62/0.58    inference(avatar_component_clause,[],[f107])).
% 1.62/0.58  fof(f107,plain,(
% 1.62/0.58    spl5_1 <=> v2_funct_1(sK2)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.62/0.58  fof(f764,plain,(
% 1.62/0.58    ~spl5_8 | ~spl5_15 | ~spl5_9 | ~spl5_10 | ~spl5_16 | ~spl5_11 | spl5_1 | spl5_17 | ~spl5_18 | ~spl5_5),
% 1.62/0.58    inference(avatar_split_clause,[],[f637,f206,f501,f497,f107,f292,f493,f288,f284,f489,f280])).
% 1.62/0.58  fof(f280,plain,(
% 1.62/0.58    spl5_8 <=> v1_funct_1(sK2)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.62/0.58  fof(f489,plain,(
% 1.62/0.58    spl5_15 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.62/0.58  fof(f284,plain,(
% 1.62/0.58    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.62/0.58  fof(f288,plain,(
% 1.62/0.58    spl5_10 <=> v1_funct_1(sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.62/0.58  fof(f493,plain,(
% 1.62/0.58    spl5_16 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.62/0.58  fof(f292,plain,(
% 1.62/0.58    spl5_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.62/0.58  fof(f501,plain,(
% 1.62/0.58    spl5_18 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.62/0.58  fof(f206,plain,(
% 1.62/0.58    spl5_5 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.62/0.58  fof(f637,plain,(
% 1.62/0.58    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl5_5),
% 1.62/0.58    inference(superposition,[],[f90,f208])).
% 1.62/0.58  fof(f208,plain,(
% 1.62/0.58    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl5_5),
% 1.62/0.58    inference(avatar_component_clause,[],[f206])).
% 1.62/0.58  fof(f90,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.62/0.58    inference(flattening,[],[f38])).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.62/0.58    inference(ennf_transformation,[],[f21])).
% 1.62/0.58  fof(f21,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.62/0.58  fof(f759,plain,(
% 1.62/0.58    ~spl5_21 | ~spl5_32 | spl5_2 | ~spl5_29),
% 1.62/0.58    inference(avatar_split_clause,[],[f756,f662,f111,f691,f552])).
% 1.62/0.58  fof(f552,plain,(
% 1.62/0.58    spl5_21 <=> v1_relat_1(sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.62/0.58  fof(f691,plain,(
% 1.62/0.58    spl5_32 <=> v5_relat_1(sK3,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.62/0.58  fof(f111,plain,(
% 1.62/0.58    spl5_2 <=> v2_funct_2(sK3,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.62/0.58  fof(f662,plain,(
% 1.62/0.58    spl5_29 <=> sK0 = k2_relat_1(sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.62/0.58  fof(f756,plain,(
% 1.62/0.58    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl5_29),
% 1.62/0.58    inference(superposition,[],[f100,f663])).
% 1.62/0.58  fof(f663,plain,(
% 1.62/0.58    sK0 = k2_relat_1(sK3) | ~spl5_29),
% 1.62/0.58    inference(avatar_component_clause,[],[f662])).
% 1.62/0.58  fof(f100,plain,(
% 1.62/0.58    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(equality_resolution,[],[f77])).
% 1.62/0.58  fof(f77,plain,(
% 1.62/0.58    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f48])).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(nnf_transformation,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.62/0.58    inference(flattening,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.62/0.58    inference(ennf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,axiom,(
% 1.62/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.62/0.58  fof(f741,plain,(
% 1.62/0.58    ~spl5_11 | spl5_29 | ~spl5_25),
% 1.62/0.58    inference(avatar_split_clause,[],[f739,f640,f662,f292])).
% 1.62/0.58  fof(f640,plain,(
% 1.62/0.58    spl5_25 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.62/0.58  fof(f739,plain,(
% 1.62/0.58    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_25),
% 1.62/0.58    inference(superposition,[],[f85,f642])).
% 1.62/0.58  fof(f642,plain,(
% 1.62/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl5_25),
% 1.62/0.58    inference(avatar_component_clause,[],[f640])).
% 1.62/0.58  fof(f85,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.62/0.58  fof(f727,plain,(
% 1.62/0.58    ~spl5_5 | spl5_26),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f725])).
% 1.62/0.58  fof(f725,plain,(
% 1.62/0.58    $false | (~spl5_5 | spl5_26)),
% 1.62/0.58    inference(resolution,[],[f646,f304])).
% 1.62/0.58  fof(f304,plain,(
% 1.62/0.58    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | ~spl5_5),
% 1.62/0.58    inference(backward_demodulation,[],[f62,f208])).
% 1.62/0.58  fof(f62,plain,(
% 1.62/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f646,plain,(
% 1.62/0.58    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | spl5_26),
% 1.62/0.58    inference(avatar_component_clause,[],[f644])).
% 1.62/0.58  fof(f644,plain,(
% 1.62/0.58    spl5_26 <=> r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.62/0.58  fof(f716,plain,(
% 1.62/0.58    spl5_32),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f714])).
% 1.62/0.58  fof(f714,plain,(
% 1.62/0.58    $false | spl5_32),
% 1.62/0.58    inference(resolution,[],[f695,f61])).
% 1.62/0.58  fof(f61,plain,(
% 1.62/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f695,plain,(
% 1.62/0.58    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl5_32),
% 1.62/0.58    inference(resolution,[],[f693,f87])).
% 1.62/0.58  fof(f87,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.62/0.58  fof(f693,plain,(
% 1.62/0.58    ~v5_relat_1(sK3,sK0) | spl5_32),
% 1.62/0.58    inference(avatar_component_clause,[],[f691])).
% 1.62/0.58  fof(f647,plain,(
% 1.62/0.58    ~spl5_10 | ~spl5_16 | ~spl5_11 | ~spl5_8 | ~spl5_15 | ~spl5_9 | spl5_25 | ~spl5_26 | ~spl5_5),
% 1.62/0.58    inference(avatar_split_clause,[],[f638,f206,f644,f640,f284,f489,f280,f292,f493,f288])).
% 1.62/0.58  fof(f638,plain,(
% 1.62/0.58    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl5_5),
% 1.62/0.58    inference(superposition,[],[f88,f208])).
% 1.62/0.58  fof(f88,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f36])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.62/0.58    inference(flattening,[],[f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.62/0.58    inference(ennf_transformation,[],[f20])).
% 1.62/0.58  fof(f20,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.62/0.58  fof(f588,plain,(
% 1.62/0.58    spl5_21),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f585])).
% 1.62/0.58  fof(f585,plain,(
% 1.62/0.58    $false | spl5_21),
% 1.62/0.58    inference(resolution,[],[f560,f61])).
% 1.62/0.58  fof(f560,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl5_21),
% 1.62/0.58    inference(resolution,[],[f554,f84])).
% 1.62/0.58  fof(f84,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f32])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(ennf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.62/0.58  fof(f554,plain,(
% 1.62/0.58    ~v1_relat_1(sK3) | spl5_21),
% 1.62/0.58    inference(avatar_component_clause,[],[f552])).
% 1.62/0.58  fof(f532,plain,(
% 1.62/0.58    spl5_16),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f531])).
% 1.62/0.58  fof(f531,plain,(
% 1.62/0.58    $false | spl5_16),
% 1.62/0.58    inference(resolution,[],[f495,f60])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f495,plain,(
% 1.62/0.58    ~v1_funct_2(sK3,sK1,sK0) | spl5_16),
% 1.62/0.58    inference(avatar_component_clause,[],[f493])).
% 1.62/0.58  fof(f530,plain,(
% 1.62/0.58    spl5_15),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f529])).
% 1.62/0.58  fof(f529,plain,(
% 1.62/0.58    $false | spl5_15),
% 1.62/0.58    inference(resolution,[],[f491,f57])).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f491,plain,(
% 1.62/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl5_15),
% 1.62/0.58    inference(avatar_component_clause,[],[f489])).
% 1.62/0.58  fof(f518,plain,(
% 1.62/0.58    spl5_18),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f517])).
% 1.62/0.58  fof(f517,plain,(
% 1.62/0.58    $false | spl5_18),
% 1.62/0.58    inference(resolution,[],[f503,f98])).
% 1.62/0.58  fof(f503,plain,(
% 1.62/0.58    ~v2_funct_1(k6_partfun1(sK0)) | spl5_18),
% 1.62/0.58    inference(avatar_component_clause,[],[f501])).
% 1.62/0.58  fof(f303,plain,(
% 1.62/0.58    spl5_11),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f302])).
% 1.62/0.58  fof(f302,plain,(
% 1.62/0.58    $false | spl5_11),
% 1.62/0.58    inference(resolution,[],[f294,f61])).
% 1.62/0.58  fof(f294,plain,(
% 1.62/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_11),
% 1.62/0.58    inference(avatar_component_clause,[],[f292])).
% 1.62/0.58  fof(f301,plain,(
% 1.62/0.58    spl5_9),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f300])).
% 1.62/0.58  fof(f300,plain,(
% 1.62/0.58    $false | spl5_9),
% 1.62/0.58    inference(resolution,[],[f286,f58])).
% 1.62/0.58  fof(f286,plain,(
% 1.62/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_9),
% 1.62/0.58    inference(avatar_component_clause,[],[f284])).
% 1.62/0.58  fof(f299,plain,(
% 1.62/0.58    spl5_10),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f298])).
% 1.62/0.58  fof(f298,plain,(
% 1.62/0.58    $false | spl5_10),
% 1.62/0.58    inference(resolution,[],[f290,f59])).
% 1.62/0.58  fof(f59,plain,(
% 1.62/0.58    v1_funct_1(sK3)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f290,plain,(
% 1.62/0.58    ~v1_funct_1(sK3) | spl5_10),
% 1.62/0.58    inference(avatar_component_clause,[],[f288])).
% 1.62/0.58  fof(f297,plain,(
% 1.62/0.58    spl5_8),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f296])).
% 1.62/0.58  fof(f296,plain,(
% 1.62/0.58    $false | spl5_8),
% 1.62/0.58    inference(resolution,[],[f282,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    v1_funct_1(sK2)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  fof(f282,plain,(
% 1.62/0.58    ~v1_funct_1(sK2) | spl5_8),
% 1.62/0.58    inference(avatar_component_clause,[],[f280])).
% 1.62/0.58  fof(f295,plain,(
% 1.62/0.58    ~spl5_8 | ~spl5_9 | ~spl5_10 | ~spl5_11 | spl5_3),
% 1.62/0.58    inference(avatar_split_clause,[],[f278,f198,f292,f288,f284,f280])).
% 1.62/0.58  fof(f198,plain,(
% 1.62/0.58    spl5_3 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.62/0.58  fof(f278,plain,(
% 1.62/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl5_3),
% 1.62/0.58    inference(resolution,[],[f95,f200])).
% 1.62/0.58  fof(f200,plain,(
% 1.62/0.58    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_3),
% 1.62/0.58    inference(avatar_component_clause,[],[f198])).
% 1.62/0.58  fof(f95,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f43])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.62/0.58    inference(flattening,[],[f42])).
% 1.62/0.58  fof(f42,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.62/0.58    inference(ennf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.62/0.58  fof(f211,plain,(
% 1.62/0.58    spl5_4),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f210])).
% 1.62/0.58  fof(f210,plain,(
% 1.62/0.58    $false | spl5_4),
% 1.62/0.58    inference(resolution,[],[f204,f97])).
% 1.62/0.58  fof(f204,plain,(
% 1.62/0.58    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl5_4),
% 1.62/0.58    inference(avatar_component_clause,[],[f202])).
% 1.62/0.58  fof(f202,plain,(
% 1.62/0.58    spl5_4 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.62/0.58  fof(f209,plain,(
% 1.62/0.58    ~spl5_3 | ~spl5_4 | spl5_5),
% 1.62/0.58    inference(avatar_split_clause,[],[f194,f206,f202,f198])).
% 1.62/0.58  fof(f194,plain,(
% 1.62/0.58    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.62/0.58    inference(resolution,[],[f92,f62])).
% 1.62/0.58  fof(f92,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f55])).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(nnf_transformation,[],[f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.62/0.58    inference(flattening,[],[f40])).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.62/0.58    inference(ennf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.62/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.62/0.58  fof(f114,plain,(
% 1.62/0.58    ~spl5_1 | ~spl5_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f63,f111,f107])).
% 1.62/0.58  fof(f63,plain,(
% 1.62/0.58    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.62/0.58    inference(cnf_transformation,[],[f46])).
% 1.62/0.58  % SZS output end Proof for theBenchmark
% 1.62/0.58  % (27382)------------------------------
% 1.62/0.58  % (27382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (27382)Termination reason: Refutation
% 1.62/0.58  
% 1.62/0.58  % (27382)Memory used [KB]: 6524
% 1.62/0.58  % (27382)Time elapsed: 0.162 s
% 1.62/0.58  % (27382)------------------------------
% 1.62/0.58  % (27382)------------------------------
% 1.62/0.58  % (27394)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.62/0.58  % (27369)Success in time 0.218 s
%------------------------------------------------------------------------------
