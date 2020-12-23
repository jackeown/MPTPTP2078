%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:11 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 413 expanded)
%              Number of leaves         :   23 ( 130 expanded)
%              Depth                    :   17
%              Number of atoms          :  494 (2585 expanded)
%              Number of equality atoms :  131 ( 460 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f135,f138,f461,f488,f496,f649,f762])).

fof(f762,plain,
    ( ~ spl10_1
    | spl10_12
    | ~ spl10_13
    | ~ spl10_14 ),
    inference(avatar_contradiction_clause,[],[f761])).

fof(f761,plain,
    ( $false
    | ~ spl10_1
    | spl10_12
    | ~ spl10_13
    | ~ spl10_14 ),
    inference(subsumption_resolution,[],[f760,f338])).

fof(f338,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f111,f121])).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f111,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f60,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f40,f39])).

fof(f39,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f760,plain,
    ( sK0 != k1_relat_1(sK2)
    | spl10_12
    | ~ spl10_13
    | ~ spl10_14 ),
    inference(forward_demodulation,[],[f759,f650])).

fof(f650,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl10_14 ),
    inference(backward_demodulation,[],[f365,f495])).

fof(f495,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f493])).

fof(f493,plain,
    ( spl10_14
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f365,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f63,f87])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f759,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl10_12
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f758,f136])).

fof(f136,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f116,f72])).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f116,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f60,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f758,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl10_12
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f757,f58])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f757,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_12
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f756,f378])).

fof(f378,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f370,f72])).

fof(f370,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f63,f68])).

fof(f756,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_12
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f755,f61])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f755,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl10_12
    | ~ spl10_13 ),
    inference(subsumption_resolution,[],[f754,f455])).

fof(f455,plain,
    ( sK2 != sK3
    | spl10_12 ),
    inference(avatar_component_clause,[],[f454])).

fof(f454,plain,
    ( spl10_12
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f754,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_13 ),
    inference(trivial_inequality_removal,[],[f753])).

fof(f753,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl10_13 ),
    inference(superposition,[],[f71,f695])).

fof(f695,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl10_13 ),
    inference(resolution,[],[f460,f64])).

fof(f64,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f460,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl10_13
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f649,plain,
    ( ~ spl10_2
    | spl10_12 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl10_2
    | spl10_12 ),
    inference(subsumption_resolution,[],[f647,f611])).

fof(f611,plain,
    ( k1_xboole_0 != sK3
    | ~ spl10_2
    | spl10_12 ),
    inference(backward_demodulation,[],[f455,f591])).

fof(f591,plain,
    ( k1_xboole_0 = sK2
    | ~ spl10_2 ),
    inference(resolution,[],[f573,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f573,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f530,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f530,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f445,f125])).

fof(f125,plain,
    ( k1_xboole_0 = sK1
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl10_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f445,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f444])).

fof(f444,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f401,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f401,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(X2,k2_zfmisc_1(sK0,sK1)),sK2)
      | r1_tarski(X2,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f115,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f115,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f60,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f647,plain,
    ( k1_xboole_0 = sK3
    | ~ spl10_2 ),
    inference(resolution,[],[f574,f69])).

fof(f574,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f531,f99])).

fof(f531,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl10_2 ),
    inference(backward_demodulation,[],[f447,f125])).

fof(f447,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f406,f77])).

fof(f406,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(X2,k2_zfmisc_1(sK0,sK1)),sK3)
      | r1_tarski(X2,k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f369,f78])).

fof(f369,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_zfmisc_1(sK0,sK1))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f63,f75])).

fof(f496,plain,
    ( spl10_14
    | spl10_2 ),
    inference(avatar_split_clause,[],[f371,f123,f493])).

fof(f371,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f362,f62])).

fof(f62,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f362,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f63,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f488,plain,
    ( ~ spl10_4
    | ~ spl10_12 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_12 ),
    inference(subsumption_resolution,[],[f465,f134])).

fof(f134,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl10_4
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f465,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl10_12 ),
    inference(backward_demodulation,[],[f65,f456])).

fof(f456,plain,
    ( sK2 = sK3
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f454])).

fof(f65,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f461,plain,
    ( spl10_12
    | spl10_13
    | ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f452,f123,f119,f458,f454])).

fof(f452,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f451,f378])).

fof(f451,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_2 ),
    inference(subsumption_resolution,[],[f450,f61])).

fof(f450,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_2 ),
    inference(trivial_inequality_removal,[],[f449])).

fof(f449,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl10_1
    | spl10_2 ),
    inference(superposition,[],[f348,f373])).

fof(f373,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl10_2 ),
    inference(forward_demodulation,[],[f365,f372])).

fof(f372,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl10_2 ),
    inference(subsumption_resolution,[],[f371,f124])).

fof(f124,plain,
    ( k1_xboole_0 != sK1
    | spl10_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f348,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f347,f136])).

fof(f347,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f344,f58])).

fof(f344,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl10_1 ),
    inference(superposition,[],[f70,f338])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f138,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f130,f113])).

fof(f113,plain,(
    ~ sP9(sK1,sK0) ),
    inference(resolution,[],[f60,f107])).

fof(f107,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP9(X1,X0) ) ),
    inference(general_splitting,[],[f96,f106_D])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP9(X1,X0) ) ),
    inference(cnf_transformation,[],[f106_D])).

fof(f106_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP9(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f130,plain,
    ( sP9(sK1,sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl10_3
  <=> sP9(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f135,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f112,f132,f128])).

fof(f112,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP9(sK1,sK0) ),
    inference(resolution,[],[f60,f106])).

fof(f126,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f117,f123,f119])).

fof(f117,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f108,f59])).

fof(f59,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f108,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f60,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:53:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (15507)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.51  % (15514)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (15508)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (15511)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (15515)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (15512)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (15522)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (15510)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (15509)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (15529)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (15519)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (15506)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (15521)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (15527)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (15513)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (15535)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.54  % (15534)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.54  % (15526)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (15524)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (15531)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.39/0.55  % (15533)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.55  % (15525)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.55  % (15517)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.55  % (15518)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (15520)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.55  % (15528)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.56  % (15530)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.56  % (15532)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.56  % (15514)Refutation found. Thanks to Tanya!
% 1.39/0.56  % SZS status Theorem for theBenchmark
% 1.39/0.56  % SZS output start Proof for theBenchmark
% 1.39/0.56  fof(f763,plain,(
% 1.39/0.56    $false),
% 1.39/0.56    inference(avatar_sat_refutation,[],[f126,f135,f138,f461,f488,f496,f649,f762])).
% 1.39/0.56  fof(f762,plain,(
% 1.39/0.56    ~spl10_1 | spl10_12 | ~spl10_13 | ~spl10_14),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f761])).
% 1.39/0.56  fof(f761,plain,(
% 1.39/0.56    $false | (~spl10_1 | spl10_12 | ~spl10_13 | ~spl10_14)),
% 1.39/0.56    inference(subsumption_resolution,[],[f760,f338])).
% 1.39/0.56  fof(f338,plain,(
% 1.39/0.56    sK0 = k1_relat_1(sK2) | ~spl10_1),
% 1.39/0.56    inference(forward_demodulation,[],[f111,f121])).
% 1.39/0.56  fof(f121,plain,(
% 1.39/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl10_1),
% 1.39/0.56    inference(avatar_component_clause,[],[f119])).
% 1.39/0.56  fof(f119,plain,(
% 1.39/0.56    spl10_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.39/0.56  fof(f111,plain,(
% 1.39/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.39/0.56    inference(resolution,[],[f60,f87])).
% 1.39/0.56  fof(f87,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f31])).
% 1.39/0.56  fof(f31,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f15])).
% 1.39/0.56  fof(f15,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.39/0.56  fof(f60,plain,(
% 1.39/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f41,plain,(
% 1.39/0.56    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f40,f39])).
% 1.39/0.56  fof(f39,plain,(
% 1.39/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f40,plain,(
% 1.39/0.56    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f22,plain,(
% 1.39/0.56    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.39/0.56    inference(flattening,[],[f21])).
% 1.39/0.56  fof(f21,plain,(
% 1.39/0.56    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.39/0.56    inference(ennf_transformation,[],[f19])).
% 1.39/0.56  fof(f19,negated_conjecture,(
% 1.39/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.39/0.56    inference(negated_conjecture,[],[f18])).
% 1.39/0.56  fof(f18,conjecture,(
% 1.39/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.39/0.56  fof(f760,plain,(
% 1.39/0.56    sK0 != k1_relat_1(sK2) | (spl10_12 | ~spl10_13 | ~spl10_14)),
% 1.39/0.56    inference(forward_demodulation,[],[f759,f650])).
% 1.39/0.56  fof(f650,plain,(
% 1.39/0.56    sK0 = k1_relat_1(sK3) | ~spl10_14),
% 1.39/0.56    inference(backward_demodulation,[],[f365,f495])).
% 1.39/0.56  fof(f495,plain,(
% 1.39/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl10_14),
% 1.39/0.56    inference(avatar_component_clause,[],[f493])).
% 1.39/0.56  fof(f493,plain,(
% 1.39/0.56    spl10_14 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.39/0.56  fof(f365,plain,(
% 1.39/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.39/0.56    inference(resolution,[],[f63,f87])).
% 1.39/0.56  fof(f63,plain,(
% 1.39/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f759,plain,(
% 1.39/0.56    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl10_12 | ~spl10_13)),
% 1.39/0.56    inference(subsumption_resolution,[],[f758,f136])).
% 1.39/0.56  fof(f136,plain,(
% 1.39/0.56    v1_relat_1(sK2)),
% 1.39/0.56    inference(subsumption_resolution,[],[f116,f72])).
% 1.39/0.56  fof(f72,plain,(
% 1.39/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f11])).
% 1.39/0.56  fof(f11,axiom,(
% 1.39/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.39/0.56  fof(f116,plain,(
% 1.39/0.56    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.39/0.56    inference(resolution,[],[f60,f68])).
% 1.39/0.56  fof(f68,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f23])).
% 1.39/0.56  fof(f23,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.39/0.56    inference(ennf_transformation,[],[f8])).
% 1.39/0.56  fof(f8,axiom,(
% 1.39/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.39/0.56  fof(f758,plain,(
% 1.39/0.56    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl10_12 | ~spl10_13)),
% 1.39/0.56    inference(subsumption_resolution,[],[f757,f58])).
% 1.39/0.56  fof(f58,plain,(
% 1.39/0.56    v1_funct_1(sK2)),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f757,plain,(
% 1.39/0.56    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl10_12 | ~spl10_13)),
% 1.39/0.56    inference(subsumption_resolution,[],[f756,f378])).
% 1.39/0.56  fof(f378,plain,(
% 1.39/0.56    v1_relat_1(sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f370,f72])).
% 1.39/0.56  fof(f370,plain,(
% 1.39/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.39/0.56    inference(resolution,[],[f63,f68])).
% 1.39/0.56  fof(f756,plain,(
% 1.39/0.56    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl10_12 | ~spl10_13)),
% 1.39/0.56    inference(subsumption_resolution,[],[f755,f61])).
% 1.39/0.56  fof(f61,plain,(
% 1.39/0.56    v1_funct_1(sK3)),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f755,plain,(
% 1.39/0.56    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl10_12 | ~spl10_13)),
% 1.39/0.56    inference(subsumption_resolution,[],[f754,f455])).
% 1.39/0.56  fof(f455,plain,(
% 1.39/0.56    sK2 != sK3 | spl10_12),
% 1.39/0.56    inference(avatar_component_clause,[],[f454])).
% 1.39/0.56  fof(f454,plain,(
% 1.39/0.56    spl10_12 <=> sK2 = sK3),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.39/0.56  fof(f754,plain,(
% 1.39/0.56    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl10_13),
% 1.39/0.56    inference(trivial_inequality_removal,[],[f753])).
% 1.39/0.56  fof(f753,plain,(
% 1.39/0.56    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl10_13),
% 1.39/0.56    inference(superposition,[],[f71,f695])).
% 1.39/0.56  fof(f695,plain,(
% 1.39/0.56    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl10_13),
% 1.39/0.56    inference(resolution,[],[f460,f64])).
% 1.39/0.56  fof(f64,plain,(
% 1.39/0.56    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f460,plain,(
% 1.39/0.56    r2_hidden(sK4(sK2,sK3),sK0) | ~spl10_13),
% 1.39/0.56    inference(avatar_component_clause,[],[f458])).
% 1.39/0.56  fof(f458,plain,(
% 1.39/0.56    spl10_13 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.39/0.56  fof(f71,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f43])).
% 1.39/0.56  fof(f43,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f42])).
% 1.39/0.56  fof(f42,plain,(
% 1.39/0.56    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f26,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.39/0.56    inference(flattening,[],[f25])).
% 1.39/0.56  fof(f25,plain,(
% 1.39/0.56    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f12])).
% 1.39/0.56  fof(f12,axiom,(
% 1.39/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.39/0.56  fof(f649,plain,(
% 1.39/0.56    ~spl10_2 | spl10_12),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f648])).
% 1.39/0.56  fof(f648,plain,(
% 1.39/0.56    $false | (~spl10_2 | spl10_12)),
% 1.39/0.56    inference(subsumption_resolution,[],[f647,f611])).
% 1.39/0.56  fof(f611,plain,(
% 1.39/0.56    k1_xboole_0 != sK3 | (~spl10_2 | spl10_12)),
% 1.39/0.56    inference(backward_demodulation,[],[f455,f591])).
% 1.39/0.56  fof(f591,plain,(
% 1.39/0.56    k1_xboole_0 = sK2 | ~spl10_2),
% 1.39/0.56    inference(resolution,[],[f573,f69])).
% 1.39/0.56  fof(f69,plain,(
% 1.39/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f24])).
% 1.39/0.56  fof(f24,plain,(
% 1.39/0.56    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.39/0.56    inference(ennf_transformation,[],[f3])).
% 1.39/0.56  fof(f3,axiom,(
% 1.39/0.56    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.39/0.56  fof(f573,plain,(
% 1.39/0.56    r1_tarski(sK2,k1_xboole_0) | ~spl10_2),
% 1.39/0.56    inference(forward_demodulation,[],[f530,f99])).
% 1.39/0.56  fof(f99,plain,(
% 1.39/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.39/0.56    inference(equality_resolution,[],[f85])).
% 1.39/0.56  fof(f85,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.39/0.56    inference(cnf_transformation,[],[f56])).
% 1.39/0.56  fof(f56,plain,(
% 1.39/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.56    inference(flattening,[],[f55])).
% 1.39/0.56  fof(f55,plain,(
% 1.39/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.39/0.56    inference(nnf_transformation,[],[f4])).
% 1.39/0.56  fof(f4,axiom,(
% 1.39/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.39/0.56  fof(f530,plain,(
% 1.39/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl10_2),
% 1.39/0.56    inference(backward_demodulation,[],[f445,f125])).
% 1.39/0.56  fof(f125,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | ~spl10_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f123])).
% 1.39/0.56  fof(f123,plain,(
% 1.39/0.56    spl10_2 <=> k1_xboole_0 = sK1),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.39/0.56  fof(f445,plain,(
% 1.39/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.56    inference(duplicate_literal_removal,[],[f444])).
% 1.39/0.56  fof(f444,plain,(
% 1.39/0.56    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.56    inference(resolution,[],[f401,f77])).
% 1.39/0.56  fof(f77,plain,(
% 1.39/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f48])).
% 1.39/0.56  fof(f48,plain,(
% 1.39/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 1.39/0.56  fof(f47,plain,(
% 1.39/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.39/0.56    introduced(choice_axiom,[])).
% 1.39/0.56  fof(f46,plain,(
% 1.39/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.56    inference(rectify,[],[f45])).
% 1.39/0.56  fof(f45,plain,(
% 1.39/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.39/0.56    inference(nnf_transformation,[],[f29])).
% 1.39/0.56  fof(f29,plain,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f1])).
% 1.39/0.56  fof(f1,axiom,(
% 1.39/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.56  fof(f401,plain,(
% 1.39/0.56    ( ! [X2] : (~r2_hidden(sK5(X2,k2_zfmisc_1(sK0,sK1)),sK2) | r1_tarski(X2,k2_zfmisc_1(sK0,sK1))) )),
% 1.39/0.56    inference(resolution,[],[f115,f78])).
% 1.39/0.56  fof(f78,plain,(
% 1.39/0.56    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f48])).
% 1.39/0.56  fof(f115,plain,(
% 1.39/0.56    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK2)) )),
% 1.39/0.56    inference(resolution,[],[f60,f75])).
% 1.39/0.56  fof(f75,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f28])).
% 1.39/0.56  fof(f28,plain,(
% 1.39/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.39/0.56    inference(ennf_transformation,[],[f5])).
% 1.39/0.56  fof(f5,axiom,(
% 1.39/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.39/0.56  fof(f647,plain,(
% 1.39/0.56    k1_xboole_0 = sK3 | ~spl10_2),
% 1.39/0.56    inference(resolution,[],[f574,f69])).
% 1.39/0.56  fof(f574,plain,(
% 1.39/0.56    r1_tarski(sK3,k1_xboole_0) | ~spl10_2),
% 1.39/0.56    inference(forward_demodulation,[],[f531,f99])).
% 1.39/0.56  fof(f531,plain,(
% 1.39/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl10_2),
% 1.39/0.56    inference(backward_demodulation,[],[f447,f125])).
% 1.39/0.56  fof(f447,plain,(
% 1.39/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.56    inference(duplicate_literal_removal,[],[f446])).
% 1.39/0.56  fof(f446,plain,(
% 1.39/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.39/0.56    inference(resolution,[],[f406,f77])).
% 1.39/0.56  fof(f406,plain,(
% 1.39/0.56    ( ! [X2] : (~r2_hidden(sK5(X2,k2_zfmisc_1(sK0,sK1)),sK3) | r1_tarski(X2,k2_zfmisc_1(sK0,sK1))) )),
% 1.39/0.56    inference(resolution,[],[f369,f78])).
% 1.39/0.56  fof(f369,plain,(
% 1.39/0.56    ( ! [X1] : (r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X1,sK3)) )),
% 1.39/0.56    inference(resolution,[],[f63,f75])).
% 1.39/0.56  fof(f496,plain,(
% 1.39/0.56    spl10_14 | spl10_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f371,f123,f493])).
% 1.39/0.56  fof(f371,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.39/0.56    inference(subsumption_resolution,[],[f362,f62])).
% 1.39/0.56  fof(f62,plain,(
% 1.39/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f362,plain,(
% 1.39/0.56    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.39/0.56    inference(resolution,[],[f63,f89])).
% 1.39/0.56  fof(f89,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.39/0.56    inference(cnf_transformation,[],[f57])).
% 1.39/0.56  fof(f57,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(nnf_transformation,[],[f34])).
% 1.39/0.56  fof(f34,plain,(
% 1.39/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(flattening,[],[f33])).
% 1.39/0.56  fof(f33,plain,(
% 1.39/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(ennf_transformation,[],[f17])).
% 1.39/0.56  fof(f17,axiom,(
% 1.39/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.39/0.56  fof(f488,plain,(
% 1.39/0.56    ~spl10_4 | ~spl10_12),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f487])).
% 1.39/0.56  fof(f487,plain,(
% 1.39/0.56    $false | (~spl10_4 | ~spl10_12)),
% 1.39/0.56    inference(subsumption_resolution,[],[f465,f134])).
% 1.39/0.56  fof(f134,plain,(
% 1.39/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_4),
% 1.39/0.56    inference(avatar_component_clause,[],[f132])).
% 1.39/0.56  fof(f132,plain,(
% 1.39/0.56    spl10_4 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.39/0.56  fof(f465,plain,(
% 1.39/0.56    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl10_12),
% 1.39/0.56    inference(backward_demodulation,[],[f65,f456])).
% 1.39/0.56  fof(f456,plain,(
% 1.39/0.56    sK2 = sK3 | ~spl10_12),
% 1.39/0.56    inference(avatar_component_clause,[],[f454])).
% 1.39/0.56  fof(f65,plain,(
% 1.39/0.56    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f461,plain,(
% 1.39/0.56    spl10_12 | spl10_13 | ~spl10_1 | spl10_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f452,f123,f119,f458,f454])).
% 1.39/0.56  fof(f452,plain,(
% 1.39/0.56    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | (~spl10_1 | spl10_2)),
% 1.39/0.56    inference(subsumption_resolution,[],[f451,f378])).
% 1.39/0.56  fof(f451,plain,(
% 1.39/0.56    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl10_1 | spl10_2)),
% 1.39/0.56    inference(subsumption_resolution,[],[f450,f61])).
% 1.39/0.56  fof(f450,plain,(
% 1.39/0.56    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_1 | spl10_2)),
% 1.39/0.56    inference(trivial_inequality_removal,[],[f449])).
% 1.39/0.56  fof(f449,plain,(
% 1.39/0.56    sK0 != sK0 | r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl10_1 | spl10_2)),
% 1.39/0.56    inference(superposition,[],[f348,f373])).
% 1.39/0.56  fof(f373,plain,(
% 1.39/0.56    sK0 = k1_relat_1(sK3) | spl10_2),
% 1.39/0.56    inference(forward_demodulation,[],[f365,f372])).
% 1.39/0.56  fof(f372,plain,(
% 1.39/0.56    sK0 = k1_relset_1(sK0,sK1,sK3) | spl10_2),
% 1.39/0.56    inference(subsumption_resolution,[],[f371,f124])).
% 1.39/0.56  fof(f124,plain,(
% 1.39/0.56    k1_xboole_0 != sK1 | spl10_2),
% 1.39/0.56    inference(avatar_component_clause,[],[f123])).
% 1.39/0.56  fof(f348,plain,(
% 1.39/0.56    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl10_1),
% 1.39/0.56    inference(subsumption_resolution,[],[f347,f136])).
% 1.39/0.56  fof(f347,plain,(
% 1.39/0.56    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl10_1),
% 1.39/0.56    inference(subsumption_resolution,[],[f344,f58])).
% 1.39/0.56  fof(f344,plain,(
% 1.39/0.56    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl10_1),
% 1.39/0.56    inference(superposition,[],[f70,f338])).
% 1.39/0.56  fof(f70,plain,(
% 1.39/0.56    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f43])).
% 1.39/0.56  fof(f138,plain,(
% 1.39/0.56    ~spl10_3),
% 1.39/0.56    inference(avatar_contradiction_clause,[],[f137])).
% 1.39/0.56  fof(f137,plain,(
% 1.39/0.56    $false | ~spl10_3),
% 1.39/0.56    inference(subsumption_resolution,[],[f130,f113])).
% 1.39/0.56  fof(f113,plain,(
% 1.39/0.56    ~sP9(sK1,sK0)),
% 1.39/0.56    inference(resolution,[],[f60,f107])).
% 1.39/0.56  fof(f107,plain,(
% 1.39/0.56    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP9(X1,X0)) )),
% 1.39/0.56    inference(general_splitting,[],[f96,f106_D])).
% 1.39/0.56  fof(f106,plain,(
% 1.39/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP9(X1,X0)) )),
% 1.39/0.56    inference(cnf_transformation,[],[f106_D])).
% 1.39/0.56  fof(f106_D,plain,(
% 1.39/0.56    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP9(X1,X0)) )),
% 1.39/0.56    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 1.39/0.56  fof(f96,plain,(
% 1.39/0.56    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.39/0.56    inference(cnf_transformation,[],[f38])).
% 1.39/0.56  fof(f38,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.39/0.56    inference(flattening,[],[f37])).
% 1.39/0.56  fof(f37,plain,(
% 1.39/0.56    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.39/0.56    inference(ennf_transformation,[],[f16])).
% 1.39/0.56  fof(f16,axiom,(
% 1.39/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.39/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.39/0.56  fof(f130,plain,(
% 1.39/0.56    sP9(sK1,sK0) | ~spl10_3),
% 1.39/0.56    inference(avatar_component_clause,[],[f128])).
% 1.39/0.56  fof(f128,plain,(
% 1.39/0.56    spl10_3 <=> sP9(sK1,sK0)),
% 1.39/0.56    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.39/0.56  fof(f135,plain,(
% 1.39/0.56    spl10_3 | spl10_4),
% 1.39/0.56    inference(avatar_split_clause,[],[f112,f132,f128])).
% 1.39/0.56  fof(f112,plain,(
% 1.39/0.56    r2_relset_1(sK0,sK1,sK2,sK2) | sP9(sK1,sK0)),
% 1.39/0.56    inference(resolution,[],[f60,f106])).
% 1.39/0.56  fof(f126,plain,(
% 1.39/0.56    spl10_1 | spl10_2),
% 1.39/0.56    inference(avatar_split_clause,[],[f117,f123,f119])).
% 1.39/0.56  fof(f117,plain,(
% 1.39/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.56    inference(subsumption_resolution,[],[f108,f59])).
% 1.39/0.56  fof(f59,plain,(
% 1.39/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.39/0.56    inference(cnf_transformation,[],[f41])).
% 1.39/0.56  fof(f108,plain,(
% 1.39/0.56    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.39/0.56    inference(resolution,[],[f60,f89])).
% 1.39/0.56  % SZS output end Proof for theBenchmark
% 1.39/0.56  % (15514)------------------------------
% 1.39/0.56  % (15514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (15514)Termination reason: Refutation
% 1.39/0.56  
% 1.39/0.56  % (15514)Memory used [KB]: 11001
% 1.39/0.56  % (15514)Time elapsed: 0.140 s
% 1.39/0.56  % (15514)------------------------------
% 1.39/0.56  % (15514)------------------------------
% 1.39/0.56  % (15523)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.56  % (15505)Success in time 0.2 s
%------------------------------------------------------------------------------
