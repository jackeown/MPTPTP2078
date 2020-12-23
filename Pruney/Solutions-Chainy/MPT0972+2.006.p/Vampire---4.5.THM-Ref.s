%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:05 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 361 expanded)
%              Number of leaves         :   21 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  476 (2178 expanded)
%              Number of equality atoms :  132 ( 440 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f132,f193,f200,f217,f228,f243,f289,f349,f380])).

fof(f380,plain,
    ( ~ spl7_1
    | spl7_19 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl7_1
    | spl7_19 ),
    inference(subsumption_resolution,[],[f377,f306])).

fof(f306,plain,
    ( k1_xboole_0 != sK2
    | spl7_19 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl7_19
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f377,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_1 ),
    inference(resolution,[],[f375,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f73,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f375,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f297,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f96,f86])).

fof(f86,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
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

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f297,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f292,f86])).

fof(f292,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f52,f127])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f349,plain,
    ( ~ spl7_1
    | spl7_13
    | ~ spl7_19 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl7_1
    | spl7_13
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f313,f332])).

fof(f332,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_1 ),
    inference(resolution,[],[f330,f94])).

fof(f330,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_1 ),
    inference(resolution,[],[f300,f97])).

fof(f300,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f294,f86])).

fof(f294,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_1 ),
    inference(backward_demodulation,[],[f55,f127])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f313,plain,
    ( k1_xboole_0 != sK3
    | spl7_13
    | ~ spl7_19 ),
    inference(backward_demodulation,[],[f211,f307])).

fof(f307,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f305])).

fof(f211,plain,
    ( sK2 != sK3
    | spl7_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl7_13
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f289,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11
    | spl7_13
    | ~ spl7_14 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f287,f168])).

fof(f168,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f166,f55])).

fof(f166,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_3 ),
    inference(superposition,[],[f137,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f137,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f287,plain,
    ( sK0 != k1_relat_1(sK3)
    | ~ spl7_2
    | ~ spl7_7
    | ~ spl7_11
    | spl7_13
    | ~ spl7_14 ),
    inference(forward_demodulation,[],[f286,f141])).

fof(f141,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f139,f52])).

fof(f139,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_2 ),
    inference(superposition,[],[f131,f75])).

fof(f131,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl7_2
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f286,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ spl7_7
    | ~ spl7_11
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f285,f182])).

fof(f182,plain,
    ( v1_relat_1(sK3)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f285,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f284,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f284,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f283,f159])).

fof(f159,plain,
    ( v1_relat_1(sK2)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl7_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f283,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f282,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f282,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl7_13
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f281,f211])).

fof(f281,plain,
    ( sK2 = sK3
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_14 ),
    inference(trivial_inequality_removal,[],[f280])).

fof(f280,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2))
    | sK2 = sK3
    | k1_relat_1(sK3) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_14 ),
    inference(superposition,[],[f61,f256])).

fof(f256,plain,
    ( k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2))
    | ~ spl7_14 ),
    inference(resolution,[],[f56,f216])).

fof(f216,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl7_14
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f56,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f243,plain,
    ( spl7_3
    | spl7_1 ),
    inference(avatar_split_clause,[],[f242,f125,f135])).

fof(f242,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(global_subsumption,[],[f55,f241])).

fof(f241,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f54,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f228,plain,(
    ~ spl7_13 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | ~ spl7_13 ),
    inference(subsumption_resolution,[],[f226,f52])).

fof(f226,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_13 ),
    inference(resolution,[],[f221,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(condensation,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f221,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_13 ),
    inference(backward_demodulation,[],[f57,f212])).

fof(f212,plain,
    ( sK2 = sK3
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f210])).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f217,plain,
    ( spl7_13
    | spl7_14
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f208,f181,f158,f135,f129,f214,f210])).

fof(f208,plain,
    ( r2_hidden(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(forward_demodulation,[],[f207,f168])).

fof(f207,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_11 ),
    inference(subsumption_resolution,[],[f206,f182])).

fof(f206,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f205,f168])).

fof(f205,plain,
    ( r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3))
    | sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(resolution,[],[f196,f53])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f195,f141])).

fof(f195,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f194,f50])).

fof(f194,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(X0,sK2),k1_relat_1(X0))
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl7_7 ),
    inference(resolution,[],[f159,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X1)
      | X0 = X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f200,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f197])).

fof(f197,plain,
    ( $false
    | spl7_11 ),
    inference(resolution,[],[f188,f55])).

fof(f188,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_11 ),
    inference(resolution,[],[f183,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f183,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f181])).

fof(f193,plain,(
    spl7_7 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl7_7 ),
    inference(resolution,[],[f165,f52])).

fof(f165,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl7_7 ),
    inference(resolution,[],[f160,f74])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_7 ),
    inference(avatar_component_clause,[],[f158])).

fof(f132,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f123,f129,f125])).

fof(f123,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f120,f52])).

fof(f120,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f78,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:58:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (28768)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (28746)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (28757)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (28769)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (28747)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (28749)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (28758)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (28750)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28752)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.54  % (28748)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.32/0.54  % (28745)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (28744)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.54  % (28746)Refutation found. Thanks to Tanya!
% 1.32/0.54  % SZS status Theorem for theBenchmark
% 1.32/0.54  % SZS output start Proof for theBenchmark
% 1.32/0.54  fof(f381,plain,(
% 1.32/0.54    $false),
% 1.32/0.54    inference(avatar_sat_refutation,[],[f132,f193,f200,f217,f228,f243,f289,f349,f380])).
% 1.32/0.54  fof(f380,plain,(
% 1.32/0.54    ~spl7_1 | spl7_19),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f379])).
% 1.32/0.54  fof(f379,plain,(
% 1.32/0.54    $false | (~spl7_1 | spl7_19)),
% 1.32/0.54    inference(subsumption_resolution,[],[f377,f306])).
% 1.32/0.54  fof(f306,plain,(
% 1.32/0.54    k1_xboole_0 != sK2 | spl7_19),
% 1.32/0.54    inference(avatar_component_clause,[],[f305])).
% 1.32/0.54  fof(f305,plain,(
% 1.32/0.54    spl7_19 <=> k1_xboole_0 = sK2),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.32/0.54  fof(f377,plain,(
% 1.32/0.54    k1_xboole_0 = sK2 | ~spl7_1),
% 1.32/0.54    inference(resolution,[],[f375,f94])).
% 1.32/0.54  fof(f94,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.32/0.54    inference(resolution,[],[f73,f58])).
% 1.32/0.54  fof(f58,plain,(
% 1.32/0.54    v1_xboole_0(k1_xboole_0)),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    v1_xboole_0(k1_xboole_0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.32/0.54  fof(f73,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f25])).
% 1.32/0.54  fof(f25,plain,(
% 1.32/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.32/0.54  fof(f375,plain,(
% 1.32/0.54    v1_xboole_0(sK2) | ~spl7_1),
% 1.32/0.54    inference(resolution,[],[f297,f97])).
% 1.32/0.54  fof(f97,plain,(
% 1.32/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) )),
% 1.32/0.54    inference(forward_demodulation,[],[f96,f86])).
% 1.32/0.54  fof(f86,plain,(
% 1.32/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.54    inference(equality_resolution,[],[f72])).
% 1.32/0.54  fof(f72,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.32/0.54    inference(flattening,[],[f47])).
% 1.32/0.54  fof(f47,plain,(
% 1.32/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.32/0.54    inference(nnf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.54  fof(f96,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) )),
% 1.32/0.54    inference(resolution,[],[f66,f58])).
% 1.32/0.54  fof(f66,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,axiom,(
% 1.32/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.32/0.54  fof(f297,plain,(
% 1.32/0.54    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl7_1),
% 1.32/0.54    inference(forward_demodulation,[],[f292,f86])).
% 1.32/0.54  fof(f292,plain,(
% 1.32/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_1),
% 1.32/0.54    inference(backward_demodulation,[],[f52,f127])).
% 1.32/0.54  fof(f127,plain,(
% 1.32/0.54    k1_xboole_0 = sK1 | ~spl7_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f125])).
% 1.32/0.54  fof(f125,plain,(
% 1.32/0.54    spl7_1 <=> k1_xboole_0 = sK1),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f36,f35])).
% 1.32/0.54  fof(f35,plain,(
% 1.32/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.32/0.54    inference(flattening,[],[f18])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.32/0.54    inference(ennf_transformation,[],[f17])).
% 1.32/0.54  fof(f17,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.32/0.54    inference(negated_conjecture,[],[f16])).
% 1.32/0.54  fof(f16,conjecture,(
% 1.32/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.32/0.54  fof(f349,plain,(
% 1.32/0.54    ~spl7_1 | spl7_13 | ~spl7_19),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f348])).
% 1.32/0.54  fof(f348,plain,(
% 1.32/0.54    $false | (~spl7_1 | spl7_13 | ~spl7_19)),
% 1.32/0.54    inference(subsumption_resolution,[],[f313,f332])).
% 1.32/0.54  fof(f332,plain,(
% 1.32/0.54    k1_xboole_0 = sK3 | ~spl7_1),
% 1.32/0.54    inference(resolution,[],[f330,f94])).
% 1.32/0.54  fof(f330,plain,(
% 1.32/0.54    v1_xboole_0(sK3) | ~spl7_1),
% 1.32/0.54    inference(resolution,[],[f300,f97])).
% 1.32/0.54  fof(f300,plain,(
% 1.32/0.54    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_1),
% 1.32/0.54    inference(forward_demodulation,[],[f294,f86])).
% 1.32/0.54  fof(f294,plain,(
% 1.32/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl7_1),
% 1.32/0.54    inference(backward_demodulation,[],[f55,f127])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f313,plain,(
% 1.32/0.54    k1_xboole_0 != sK3 | (spl7_13 | ~spl7_19)),
% 1.32/0.54    inference(backward_demodulation,[],[f211,f307])).
% 1.32/0.54  fof(f307,plain,(
% 1.32/0.54    k1_xboole_0 = sK2 | ~spl7_19),
% 1.32/0.54    inference(avatar_component_clause,[],[f305])).
% 1.32/0.54  fof(f211,plain,(
% 1.32/0.54    sK2 != sK3 | spl7_13),
% 1.32/0.54    inference(avatar_component_clause,[],[f210])).
% 1.32/0.54  fof(f210,plain,(
% 1.32/0.54    spl7_13 <=> sK2 = sK3),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 1.32/0.54  fof(f289,plain,(
% 1.32/0.54    ~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_11 | spl7_13 | ~spl7_14),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f288])).
% 1.32/0.54  fof(f288,plain,(
% 1.32/0.54    $false | (~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_11 | spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(subsumption_resolution,[],[f287,f168])).
% 1.32/0.54  fof(f168,plain,(
% 1.32/0.54    sK0 = k1_relat_1(sK3) | ~spl7_3),
% 1.32/0.54    inference(subsumption_resolution,[],[f166,f55])).
% 1.32/0.54  fof(f166,plain,(
% 1.32/0.54    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_3),
% 1.32/0.54    inference(superposition,[],[f137,f75])).
% 1.32/0.54  fof(f75,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f27])).
% 1.32/0.54  fof(f27,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.54    inference(ennf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.32/0.54  fof(f137,plain,(
% 1.32/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f135])).
% 1.32/0.54  fof(f135,plain,(
% 1.32/0.54    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.32/0.54  fof(f287,plain,(
% 1.32/0.54    sK0 != k1_relat_1(sK3) | (~spl7_2 | ~spl7_7 | ~spl7_11 | spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(forward_demodulation,[],[f286,f141])).
% 1.32/0.54  fof(f141,plain,(
% 1.32/0.54    sK0 = k1_relat_1(sK2) | ~spl7_2),
% 1.32/0.54    inference(subsumption_resolution,[],[f139,f52])).
% 1.32/0.54  fof(f139,plain,(
% 1.32/0.54    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_2),
% 1.32/0.54    inference(superposition,[],[f131,f75])).
% 1.32/0.54  fof(f131,plain,(
% 1.32/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f129])).
% 1.32/0.54  fof(f129,plain,(
% 1.32/0.54    spl7_2 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.32/0.54  fof(f286,plain,(
% 1.32/0.54    k1_relat_1(sK3) != k1_relat_1(sK2) | (~spl7_7 | ~spl7_11 | spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(subsumption_resolution,[],[f285,f182])).
% 1.32/0.54  fof(f182,plain,(
% 1.32/0.54    v1_relat_1(sK3) | ~spl7_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f181])).
% 1.32/0.54  fof(f181,plain,(
% 1.32/0.54    spl7_11 <=> v1_relat_1(sK3)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 1.32/0.54  fof(f285,plain,(
% 1.32/0.54    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK3) | (~spl7_7 | spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(subsumption_resolution,[],[f284,f53])).
% 1.32/0.54  fof(f53,plain,(
% 1.32/0.54    v1_funct_1(sK3)),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f284,plain,(
% 1.32/0.54    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_7 | spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(subsumption_resolution,[],[f283,f159])).
% 1.32/0.54  fof(f159,plain,(
% 1.32/0.54    v1_relat_1(sK2) | ~spl7_7),
% 1.32/0.54    inference(avatar_component_clause,[],[f158])).
% 1.32/0.54  fof(f158,plain,(
% 1.32/0.54    spl7_7 <=> v1_relat_1(sK2)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.32/0.54  fof(f283,plain,(
% 1.32/0.54    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(subsumption_resolution,[],[f282,f50])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    v1_funct_1(sK2)),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f282,plain,(
% 1.32/0.54    k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (spl7_13 | ~spl7_14)),
% 1.32/0.54    inference(subsumption_resolution,[],[f281,f211])).
% 1.32/0.54  fof(f281,plain,(
% 1.32/0.54    sK2 = sK3 | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_14),
% 1.32/0.54    inference(trivial_inequality_removal,[],[f280])).
% 1.32/0.54  fof(f280,plain,(
% 1.32/0.54    k1_funct_1(sK2,sK4(sK3,sK2)) != k1_funct_1(sK2,sK4(sK3,sK2)) | sK2 = sK3 | k1_relat_1(sK3) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl7_14),
% 1.32/0.54    inference(superposition,[],[f61,f256])).
% 1.32/0.54  fof(f256,plain,(
% 1.32/0.54    k1_funct_1(sK2,sK4(sK3,sK2)) = k1_funct_1(sK3,sK4(sK3,sK2)) | ~spl7_14),
% 1.32/0.54    inference(resolution,[],[f56,f216])).
% 1.32/0.54  fof(f216,plain,(
% 1.32/0.54    r2_hidden(sK4(sK3,sK2),sK0) | ~spl7_14),
% 1.32/0.54    inference(avatar_component_clause,[],[f214])).
% 1.32/0.54  fof(f214,plain,(
% 1.32/0.54    spl7_14 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f39])).
% 1.32/0.54  fof(f39,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.32/0.54    introduced(choice_axiom,[])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.54    inference(flattening,[],[f20])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.32/0.54  fof(f243,plain,(
% 1.32/0.54    spl7_3 | spl7_1),
% 1.32/0.54    inference(avatar_split_clause,[],[f242,f125,f135])).
% 1.32/0.54  fof(f242,plain,(
% 1.32/0.54    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.32/0.54    inference(global_subsumption,[],[f55,f241])).
% 1.32/0.54  fof(f241,plain,(
% 1.32/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f54,f78])).
% 1.32/0.54  fof(f78,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f49])).
% 1.32/0.54  fof(f49,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.54    inference(nnf_transformation,[],[f30])).
% 1.32/0.54  fof(f30,plain,(
% 1.32/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.54    inference(flattening,[],[f29])).
% 1.32/0.54  fof(f29,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.54    inference(ennf_transformation,[],[f15])).
% 1.32/0.54  fof(f15,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    v1_funct_2(sK3,sK0,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f228,plain,(
% 1.32/0.54    ~spl7_13),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f227])).
% 1.32/0.54  fof(f227,plain,(
% 1.32/0.54    $false | ~spl7_13),
% 1.32/0.54    inference(subsumption_resolution,[],[f226,f52])).
% 1.32/0.54  fof(f226,plain,(
% 1.32/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_13),
% 1.32/0.54    inference(resolution,[],[f221,f93])).
% 1.32/0.54  fof(f93,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.54    inference(condensation,[],[f85])).
% 1.32/0.54  fof(f85,plain,(
% 1.32/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f34])).
% 1.32/0.54  fof(f34,plain,(
% 1.32/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.54    inference(flattening,[],[f33])).
% 1.32/0.54  fof(f33,plain,(
% 1.32/0.54    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.32/0.54    inference(ennf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,axiom,(
% 1.32/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.32/0.54  fof(f221,plain,(
% 1.32/0.54    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_13),
% 1.32/0.54    inference(backward_demodulation,[],[f57,f212])).
% 1.32/0.54  fof(f212,plain,(
% 1.32/0.54    sK2 = sK3 | ~spl7_13),
% 1.32/0.54    inference(avatar_component_clause,[],[f210])).
% 1.32/0.54  fof(f57,plain,(
% 1.32/0.54    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  fof(f217,plain,(
% 1.32/0.54    spl7_13 | spl7_14 | ~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_11),
% 1.32/0.54    inference(avatar_split_clause,[],[f208,f181,f158,f135,f129,f214,f210])).
% 1.32/0.54  fof(f208,plain,(
% 1.32/0.54    r2_hidden(sK4(sK3,sK2),sK0) | sK2 = sK3 | (~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_11)),
% 1.32/0.54    inference(forward_demodulation,[],[f207,f168])).
% 1.32/0.54  fof(f207,plain,(
% 1.32/0.54    r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3 | (~spl7_2 | ~spl7_3 | ~spl7_7 | ~spl7_11)),
% 1.32/0.54    inference(subsumption_resolution,[],[f206,f182])).
% 1.32/0.54  fof(f206,plain,(
% 1.32/0.54    r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl7_2 | ~spl7_3 | ~spl7_7)),
% 1.32/0.54    inference(subsumption_resolution,[],[f205,f168])).
% 1.32/0.54  fof(f205,plain,(
% 1.32/0.54    r2_hidden(sK4(sK3,sK2),k1_relat_1(sK3)) | sK2 = sK3 | sK0 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_2 | ~spl7_7)),
% 1.32/0.54    inference(resolution,[],[f196,f53])).
% 1.32/0.54  fof(f196,plain,(
% 1.32/0.54    ( ! [X0] : (~v1_funct_1(X0) | r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | (~spl7_2 | ~spl7_7)),
% 1.32/0.54    inference(forward_demodulation,[],[f195,f141])).
% 1.32/0.54  fof(f195,plain,(
% 1.32/0.54    ( ! [X0] : (r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(sK2) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_7),
% 1.32/0.54    inference(subsumption_resolution,[],[f194,f50])).
% 1.32/0.54  fof(f194,plain,(
% 1.32/0.54    ( ! [X0] : (r2_hidden(sK4(X0,sK2),k1_relat_1(X0)) | k1_relat_1(X0) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl7_7),
% 1.32/0.54    inference(resolution,[],[f159,f60])).
% 1.32/0.54  fof(f60,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | X0 = X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f39])).
% 1.32/0.54  fof(f200,plain,(
% 1.32/0.54    spl7_11),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f197])).
% 1.32/0.54  fof(f197,plain,(
% 1.32/0.54    $false | spl7_11),
% 1.32/0.54    inference(resolution,[],[f188,f55])).
% 1.32/0.54  fof(f188,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_11),
% 1.32/0.54    inference(resolution,[],[f183,f74])).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.54    inference(cnf_transformation,[],[f26])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.54    inference(ennf_transformation,[],[f10])).
% 1.32/0.54  fof(f10,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.32/0.54  fof(f183,plain,(
% 1.32/0.54    ~v1_relat_1(sK3) | spl7_11),
% 1.32/0.54    inference(avatar_component_clause,[],[f181])).
% 1.32/0.54  fof(f193,plain,(
% 1.32/0.54    spl7_7),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f190])).
% 1.32/0.54  fof(f190,plain,(
% 1.32/0.54    $false | spl7_7),
% 1.32/0.54    inference(resolution,[],[f165,f52])).
% 1.32/0.54  fof(f165,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl7_7),
% 1.32/0.54    inference(resolution,[],[f160,f74])).
% 1.32/0.54  fof(f160,plain,(
% 1.32/0.54    ~v1_relat_1(sK2) | spl7_7),
% 1.32/0.54    inference(avatar_component_clause,[],[f158])).
% 1.32/0.54  fof(f132,plain,(
% 1.32/0.54    spl7_1 | spl7_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f123,f129,f125])).
% 1.32/0.54  fof(f123,plain,(
% 1.32/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1),
% 1.32/0.54    inference(subsumption_resolution,[],[f120,f52])).
% 1.32/0.54  fof(f120,plain,(
% 1.32/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.54    inference(resolution,[],[f78,f51])).
% 1.32/0.54  fof(f51,plain,(
% 1.32/0.54    v1_funct_2(sK2,sK0,sK1)),
% 1.32/0.54    inference(cnf_transformation,[],[f37])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (28746)------------------------------
% 1.32/0.54  % (28746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (28746)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (28746)Memory used [KB]: 10874
% 1.32/0.54  % (28746)Time elapsed: 0.122 s
% 1.32/0.54  % (28746)------------------------------
% 1.32/0.54  % (28746)------------------------------
% 1.32/0.55  % (28741)Success in time 0.181 s
%------------------------------------------------------------------------------
