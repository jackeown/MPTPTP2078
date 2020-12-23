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
% DateTime   : Thu Dec  3 13:06:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 302 expanded)
%              Number of leaves         :   28 ( 106 expanded)
%              Depth                    :   20
%              Number of atoms          :  525 ( 957 expanded)
%              Number of equality atoms :   35 (  81 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f73,f78,f91,f101,f113,f136,f145,f167,f188,f212,f222,f253,f265,f607,f609])).

fof(f609,plain,
    ( sK0 != k1_relat_1(sK3)
    | v1_xboole_0(k1_relat_1(sK3))
    | ~ v1_xboole_0(sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

% (12770)Termination reason: Refutation not found, incomplete strategy
fof(f607,plain,
    ( ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_9
    | spl10_14
    | spl10_16
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f606])).

% (12770)Memory used [KB]: 11001
% (12770)Time elapsed: 0.102 s
% (12770)------------------------------
% (12770)------------------------------
fof(f606,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_9
    | spl10_14
    | spl10_16
    | spl10_19 ),
    inference(trivial_inequality_removal,[],[f603])).

fof(f603,plain,
    ( sK4 != sK4
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | ~ spl10_9
    | spl10_14
    | spl10_16
    | spl10_19 ),
    inference(resolution,[],[f601,f135])).

fof(f135,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl10_9
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f601,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | sK4 != X0 )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | spl10_14
    | spl10_16
    | spl10_19 ),
    inference(subsumption_resolution,[],[f600,f221])).

fof(f221,plain,
    ( ~ v1_xboole_0(sK2)
    | spl10_19 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl10_19
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f600,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | v1_xboole_0(sK2) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | spl10_14
    | spl10_16 ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK2)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2)) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | spl10_14
    | spl10_16 ),
    inference(resolution,[],[f526,f439])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK5(X0,sK0,sK3,X1),X0)
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(condensation,[],[f438])).

fof(f438,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | r2_hidden(sK5(X0,sK0,sK3,X1),X0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(forward_demodulation,[],[f437,f85])).

fof(f85,plain,
    ( ! [X3] : k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)
    | ~ spl10_3 ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl10_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f437,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0,sK0,sK3,X1),X0)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(subsumption_resolution,[],[f436,f166])).

fof(f166,plain,
    ( ~ v1_xboole_0(sK0)
    | spl10_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl10_14
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f436,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | r2_hidden(sK5(X0,sK0,sK3,X1),X0)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_16 ),
    inference(resolution,[],[f360,f72])).

fof(f360,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X2)
        | r2_hidden(sK5(X2,X0,X1,X3),X2)
        | ~ r2_hidden(X3,k7_relset_1(X0,sK1,X1,X2))
        | ~ r2_hidden(X3,k9_relat_1(sK3,X4)) )
    | ~ spl10_3
    | spl10_16 ),
    inference(resolution,[],[f194,f189])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,sK1)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl10_3 ),
    inference(forward_demodulation,[],[f114,f85])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1))
        | m1_subset_1(X0,sK1) )
    | ~ spl10_3 ),
    inference(resolution,[],[f84,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f84,plain,
    ( ! [X2] : m1_subset_1(k7_relset_1(sK0,sK1,sK3,X2),k1_zfmisc_1(sK1))
    | ~ spl10_3 ),
    inference(resolution,[],[f72,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f194,plain,
    ( ! [X12,X10,X11,X9] :
        ( ~ m1_subset_1(X12,sK1)
        | v1_xboole_0(X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1)))
        | v1_xboole_0(X9)
        | r2_hidden(sK5(X9,X10,X11,X12),X9)
        | ~ r2_hidden(X12,k7_relset_1(X10,sK1,X11,X9)) )
    | spl10_16 ),
    inference(resolution,[],[f187,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(sK5(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f187,plain,
    ( ~ v1_xboole_0(sK1)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl10_16
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f526,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK5(X0,sK0,sK3,X1),sK2)
        | sK4 != X1
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | spl10_14
    | spl10_16 ),
    inference(subsumption_resolution,[],[f525,f430])).

fof(f430,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(condensation,[],[f429])).

fof(f429,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(forward_demodulation,[],[f428,f85])).

fof(f428,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(subsumption_resolution,[],[f427,f166])).

fof(f427,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_16 ),
    inference(resolution,[],[f358,f72])).

fof(f358,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X2)
        | m1_subset_1(sK5(X2,X0,X1,X3),X0)
        | ~ r2_hidden(X3,k7_relset_1(X0,sK1,X1,X2))
        | ~ r2_hidden(X3,k9_relat_1(sK3,X4)) )
    | ~ spl10_3
    | spl10_16 ),
    inference(resolution,[],[f192,f189])).

fof(f192,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ m1_subset_1(X4,sK1)
        | v1_xboole_0(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
        | v1_xboole_0(X1)
        | m1_subset_1(sK5(X1,X2,X3,X4),X2)
        | ~ r2_hidden(X4,k7_relset_1(X2,sK1,X3,X1)) )
    | spl10_16 ),
    inference(resolution,[],[f187,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | m1_subset_1(sK5(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f525,plain,
    ( ! [X0,X1] :
        ( sK4 != X1
        | ~ r2_hidden(sK5(X0,sK0,sK3,X1),sK2)
        | ~ m1_subset_1(sK5(X0,sK0,sK3,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | spl10_14
    | spl10_16 ),
    inference(superposition,[],[f28,f494])).

fof(f494,plain,
    ( ! [X4,X3] :
        ( k1_funct_1(sK3,sK5(X3,sK0,sK3,X4)) = X4
        | ~ r2_hidden(X4,k9_relat_1(sK3,X3))
        | v1_xboole_0(X3) )
    | ~ spl10_1
    | ~ spl10_3
    | ~ spl10_5
    | spl10_14
    | spl10_16 ),
    inference(resolution,[],[f452,f150])).

fof(f150,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
        | k1_funct_1(sK3,X2) = X3 )
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f62,f90])).

fof(f90,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl10_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f62,plain,
    ( ! [X2,X3] :
        ( ~ v1_relat_1(sK3)
        | k1_funct_1(sK3,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK3) )
    | ~ spl10_1 ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f59,plain,
    ( v1_funct_1(sK3)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl10_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f452,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(condensation,[],[f451])).

fof(f451,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X1,k9_relat_1(sK3,X0))
        | v1_xboole_0(X0)
        | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(forward_demodulation,[],[f450,f85])).

fof(f450,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_14
    | spl10_16 ),
    inference(subsumption_resolution,[],[f449,f166])).

fof(f449,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3)
        | ~ r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0))
        | ~ r2_hidden(X1,k9_relat_1(sK3,X2)) )
    | ~ spl10_3
    | spl10_16 ),
    inference(resolution,[],[f366,f72])).

fof(f366,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | v1_xboole_0(X0)
        | v1_xboole_0(X2)
        | r2_hidden(k4_tarski(sK5(X2,X0,X1,X3),X3),X1)
        | ~ r2_hidden(X3,k7_relset_1(X0,sK1,X1,X2))
        | ~ r2_hidden(X3,k9_relat_1(sK3,X4)) )
    | ~ spl10_3
    | spl10_16 ),
    inference(resolution,[],[f193,f189])).

fof(f193,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ m1_subset_1(X8,sK1)
        | v1_xboole_0(X6)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,sK1)))
        | v1_xboole_0(X5)
        | r2_hidden(k4_tarski(sK5(X5,X6,X7,X8),X8),X7)
        | ~ r2_hidden(X8,k7_relset_1(X6,sK1,X7,X5)) )
    | spl10_16 ),
    inference(resolution,[],[f187,f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ m1_subset_1(X4,X0)
      | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f28,plain,(
    ! [X5] :
      ( sK4 != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f265,plain,
    ( ~ spl10_23
    | ~ spl10_21 ),
    inference(avatar_split_clause,[],[f255,f250,f262])).

fof(f262,plain,
    ( spl10_23
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f250,plain,
    ( spl10_21
  <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f255,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | ~ spl10_21 ),
    inference(resolution,[],[f252,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f252,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f250])).

fof(f253,plain,
    ( spl10_21
    | ~ spl10_5
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f204,f133,f88,f250])).

fof(f204,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))
    | ~ spl10_5
    | ~ spl10_9 ),
    inference(resolution,[],[f93,f135])).

fof(f93,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK7(X0,X1,sK3),k1_relat_1(sK3)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f90,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f222,plain,
    ( ~ spl10_19
    | ~ spl10_18 ),
    inference(avatar_split_clause,[],[f214,f209,f219])).

fof(f209,plain,
    ( spl10_18
  <=> r2_hidden(sK7(sK4,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f214,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl10_18 ),
    inference(resolution,[],[f211,f39])).

fof(f211,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f209])).

fof(f212,plain,
    ( spl10_18
    | ~ spl10_5
    | ~ spl10_9 ),
    inference(avatar_split_clause,[],[f202,f133,f88,f209])).

fof(f202,plain,
    ( r2_hidden(sK7(sK4,sK2,sK3),sK2)
    | ~ spl10_5
    | ~ spl10_9 ),
    inference(resolution,[],[f95,f135])).

fof(f95,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,k9_relat_1(sK3,X5))
        | r2_hidden(sK7(X4,X5,sK3),X5) )
    | ~ spl10_5 ),
    inference(resolution,[],[f90,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(sK7(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f188,plain,
    ( ~ spl10_16
    | ~ spl10_3
    | spl10_6 ),
    inference(avatar_split_clause,[],[f183,f98,f70,f185])).

fof(f98,plain,
    ( spl10_6
  <=> v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f183,plain,
    ( ~ v1_xboole_0(sK1)
    | ~ spl10_3
    | spl10_6 ),
    inference(resolution,[],[f182,f117])).

fof(f117,plain,
    ( ! [X0] : m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))
    | ~ spl10_3 ),
    inference(superposition,[],[f84,f85])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl10_3
    | spl10_6 ),
    inference(forward_demodulation,[],[f103,f85])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | spl10_6 ),
    inference(resolution,[],[f100,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f100,plain,
    ( ~ v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2))
    | spl10_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f167,plain,
    ( ~ spl10_14
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f161,f138,f164])).

fof(f138,plain,
    ( spl10_10
  <=> r2_hidden(sK8(sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f161,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl10_10 ),
    inference(resolution,[],[f140,f39])).

fof(f140,plain,
    ( r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f145,plain,
    ( spl10_10
    | spl10_11
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f131,f110,f70,f142,f138])).

fof(f142,plain,
    ( spl10_11
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).

fof(f110,plain,
    ( spl10_7
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f131,plain,
    ( sK0 = k1_relat_1(sK3)
    | r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_3
    | ~ spl10_7 ),
    inference(forward_demodulation,[],[f81,f112])).

fof(f112,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f81,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK8(sK0,sK3),sK0)
    | ~ spl10_3 ),
    inference(resolution,[],[f72,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k1_relset_1(X1,X0,X2) = X1
      | r2_hidden(sK8(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X3,X4),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X3,X4),X2)
              & r2_hidden(X3,X1) )
      <=> k1_relset_1(X1,X0,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).

fof(f136,plain,
    ( spl10_9
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f116,f75,f70,f133])).

fof(f75,plain,
    ( spl10_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f116,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl10_3
    | ~ spl10_4 ),
    inference(superposition,[],[f77,f85])).

fof(f77,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f75])).

fof(f113,plain,
    ( spl10_7
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f80,f70,f110])).

fof(f80,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl10_3 ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f101,plain,
    ( ~ spl10_6
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f92,f75,f98])).

fof(f92,plain,
    ( ~ v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl10_4 ),
    inference(resolution,[],[f77,f39])).

fof(f91,plain,
    ( spl10_5
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f79,f70,f88])).

fof(f79,plain,
    ( v1_relat_1(sK3)
    | ~ spl10_3 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

% (12779)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f78,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f73,plain,(
    spl10_3 ),
    inference(avatar_split_clause,[],[f32,f70])).

fof(f32,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f60,plain,(
    spl10_1 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:15:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (12773)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (12774)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (12765)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (12766)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (12763)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (12762)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (12761)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (12770)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (12768)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (12760)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12760)Refutation not found, incomplete strategy% (12760)------------------------------
% 0.21/0.50  % (12760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12760)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12760)Memory used [KB]: 10618
% 0.21/0.50  % (12760)Time elapsed: 0.090 s
% 0.21/0.50  % (12760)------------------------------
% 0.21/0.50  % (12760)------------------------------
% 0.21/0.50  % (12771)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12764)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (12759)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (12776)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (12778)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (12777)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (12772)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (12770)Refutation not found, incomplete strategy% (12770)------------------------------
% 0.21/0.51  % (12770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12767)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (12762)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f610,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f60,f73,f78,f91,f101,f113,f136,f145,f167,f188,f212,f222,f253,f265,f607,f609])).
% 0.21/0.51  fof(f609,plain,(
% 0.21/0.51    sK0 != k1_relat_1(sK3) | v1_xboole_0(k1_relat_1(sK3)) | ~v1_xboole_0(sK0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  % (12770)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  fof(f607,plain,(
% 0.21/0.51    ~spl10_1 | ~spl10_3 | ~spl10_5 | ~spl10_9 | spl10_14 | spl10_16 | spl10_19),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f606])).
% 0.21/0.51  
% 0.21/0.51  % (12770)Memory used [KB]: 11001
% 0.21/0.51  % (12770)Time elapsed: 0.102 s
% 0.21/0.51  % (12770)------------------------------
% 0.21/0.51  % (12770)------------------------------
% 0.21/0.51  fof(f606,plain,(
% 0.21/0.51    $false | (~spl10_1 | ~spl10_3 | ~spl10_5 | ~spl10_9 | spl10_14 | spl10_16 | spl10_19)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f603])).
% 0.21/0.51  fof(f603,plain,(
% 0.21/0.51    sK4 != sK4 | (~spl10_1 | ~spl10_3 | ~spl10_5 | ~spl10_9 | spl10_14 | spl10_16 | spl10_19)),
% 0.21/0.51    inference(resolution,[],[f601,f135])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl10_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f133])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    spl10_9 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.51  fof(f601,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k9_relat_1(sK3,sK2)) | sK4 != X0) ) | (~spl10_1 | ~spl10_3 | ~spl10_5 | spl10_14 | spl10_16 | spl10_19)),
% 0.21/0.51    inference(subsumption_resolution,[],[f600,f221])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | spl10_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f219])).
% 0.21/0.51  fof(f219,plain,(
% 0.21/0.51    spl10_19 <=> v1_xboole_0(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.21/0.51  fof(f600,plain,(
% 0.21/0.51    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | v1_xboole_0(sK2)) ) | (~spl10_1 | ~spl10_3 | ~spl10_5 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f599])).
% 0.21/0.51  fof(f599,plain,(
% 0.21/0.51    ( ! [X0] : (sK4 != X0 | ~r2_hidden(X0,k9_relat_1(sK3,sK2)) | v1_xboole_0(sK2) | v1_xboole_0(sK2) | ~r2_hidden(X0,k9_relat_1(sK3,sK2))) ) | (~spl10_1 | ~spl10_3 | ~spl10_5 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f526,f439])).
% 0.21/0.51  fof(f439,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK5(X0,sK0,sK3,X1),X0) | v1_xboole_0(X0) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(condensation,[],[f438])).
% 0.21/0.51  fof(f438,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | r2_hidden(sK5(X0,sK0,sK3,X1),X0) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(forward_demodulation,[],[f437,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X3] : (k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)) ) | ~spl10_3),
% 0.21/0.51    inference(resolution,[],[f72,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl10_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    spl10_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.51  fof(f437,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | r2_hidden(sK5(X0,sK0,sK3,X1),X0) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f436,f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | spl10_14),
% 0.21/0.51    inference(avatar_component_clause,[],[f164])).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    spl10_14 <=> v1_xboole_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | r2_hidden(sK5(X0,sK0,sK3,X1),X0) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f360,f72])).
% 0.21/0.51  fof(f360,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | v1_xboole_0(X2) | r2_hidden(sK5(X2,X0,X1,X3),X2) | ~r2_hidden(X3,k7_relset_1(X0,sK1,X1,X2)) | ~r2_hidden(X3,k9_relat_1(sK3,X4))) ) | (~spl10_3 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f194,f189])).
% 0.21/0.51  fof(f189,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(X0,sK1) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl10_3),
% 0.21/0.51    inference(forward_demodulation,[],[f114,f85])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k7_relset_1(sK0,sK1,sK3,X1)) | m1_subset_1(X0,sK1)) ) | ~spl10_3),
% 0.21/0.51    inference(resolution,[],[f84,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X2] : (m1_subset_1(k7_relset_1(sK0,sK1,sK3,X2),k1_zfmisc_1(sK1))) ) | ~spl10_3),
% 0.21/0.51    inference(resolution,[],[f72,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    ( ! [X12,X10,X11,X9] : (~m1_subset_1(X12,sK1) | v1_xboole_0(X10) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X10,sK1))) | v1_xboole_0(X9) | r2_hidden(sK5(X9,X10,X11,X12),X9) | ~r2_hidden(X12,k7_relset_1(X10,sK1,X11,X9))) ) | spl10_16),
% 0.21/0.51    inference(resolution,[],[f187,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(sK5(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1) | spl10_16),
% 0.21/0.51    inference(avatar_component_clause,[],[f185])).
% 0.21/0.51  fof(f185,plain,(
% 0.21/0.51    spl10_16 <=> v1_xboole_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.51  fof(f526,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(sK5(X0,sK0,sK3,X1),sK2) | sK4 != X1 | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0)) ) | (~spl10_1 | ~spl10_3 | ~spl10_5 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f525,f430])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | v1_xboole_0(X0) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(condensation,[],[f429])).
% 0.21/0.51  fof(f429,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(forward_demodulation,[],[f428,f85])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f427,f166])).
% 0.21/0.51  fof(f427,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f358,f72])).
% 0.21/0.51  fof(f358,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | v1_xboole_0(X2) | m1_subset_1(sK5(X2,X0,X1,X3),X0) | ~r2_hidden(X3,k7_relset_1(X0,sK1,X1,X2)) | ~r2_hidden(X3,k9_relat_1(sK3,X4))) ) | (~spl10_3 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f192,f189])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ( ! [X4,X2,X3,X1] : (~m1_subset_1(X4,sK1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | v1_xboole_0(X1) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,sK1,X3,X1))) ) | spl10_16),
% 0.21/0.51    inference(resolution,[],[f187,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | m1_subset_1(sK5(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f525,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sK4 != X1 | ~r2_hidden(sK5(X0,sK0,sK3,X1),sK2) | ~m1_subset_1(sK5(X0,sK0,sK3,X1),sK0) | ~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0)) ) | (~spl10_1 | ~spl10_3 | ~spl10_5 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(superposition,[],[f28,f494])).
% 0.21/0.51  fof(f494,plain,(
% 0.21/0.51    ( ! [X4,X3] : (k1_funct_1(sK3,sK5(X3,sK0,sK3,X4)) = X4 | ~r2_hidden(X4,k9_relat_1(sK3,X3)) | v1_xboole_0(X3)) ) | (~spl10_1 | ~spl10_3 | ~spl10_5 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f452,f150])).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | k1_funct_1(sK3,X2) = X3) ) | (~spl10_1 | ~spl10_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f62,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl10_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl10_5 <=> v1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~v1_relat_1(sK3) | k1_funct_1(sK3,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK3)) ) | ~spl10_1),
% 0.21/0.51    inference(resolution,[],[f59,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    v1_funct_1(sK3) | ~spl10_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl10_1 <=> v1_funct_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.51  fof(f452,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | v1_xboole_0(X0) | ~r2_hidden(X1,k9_relat_1(sK3,X0))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(condensation,[],[f451])).
% 0.21/0.51  fof(f451,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X1,k9_relat_1(sK3,X0)) | v1_xboole_0(X0) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(forward_demodulation,[],[f450,f85])).
% 0.21/0.51  fof(f450,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_14 | spl10_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f449,f166])).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | r2_hidden(k4_tarski(sK5(X0,sK0,sK3,X1),X1),sK3) | ~r2_hidden(X1,k7_relset_1(sK0,sK1,sK3,X0)) | ~r2_hidden(X1,k9_relat_1(sK3,X2))) ) | (~spl10_3 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f366,f72])).
% 0.21/0.51  fof(f366,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | v1_xboole_0(X0) | v1_xboole_0(X2) | r2_hidden(k4_tarski(sK5(X2,X0,X1,X3),X3),X1) | ~r2_hidden(X3,k7_relset_1(X0,sK1,X1,X2)) | ~r2_hidden(X3,k9_relat_1(sK3,X4))) ) | (~spl10_3 | spl10_16)),
% 0.21/0.51    inference(resolution,[],[f193,f189])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X8,sK1) | v1_xboole_0(X6) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X6,sK1))) | v1_xboole_0(X5) | r2_hidden(k4_tarski(sK5(X5,X6,X7,X8),X8),X7) | ~r2_hidden(X8,k7_relset_1(X6,sK1,X7,X5))) ) | spl10_16),
% 0.21/0.51    inference(resolution,[],[f187,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~m1_subset_1(X4,X0) | r2_hidden(k4_tarski(sK5(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X5] : (sK4 != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.51  fof(f265,plain,(
% 0.21/0.51    ~spl10_23 | ~spl10_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f255,f250,f262])).
% 0.21/0.51  fof(f262,plain,(
% 0.21/0.51    spl10_23 <=> v1_xboole_0(k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    spl10_21 <=> r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    ~v1_xboole_0(k1_relat_1(sK3)) | ~spl10_21),
% 0.21/0.51    inference(resolution,[],[f252,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | ~spl10_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f250])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    spl10_21 | ~spl10_5 | ~spl10_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f204,f133,f88,f250])).
% 0.21/0.51  fof(f204,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),k1_relat_1(sK3)) | (~spl10_5 | ~spl10_9)),
% 0.21/0.51    inference(resolution,[],[f93,f135])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK7(X0,X1,sK3),k1_relat_1(sK3))) ) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f90,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK7(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.21/0.51  fof(f222,plain,(
% 0.21/0.51    ~spl10_19 | ~spl10_18),
% 0.21/0.51    inference(avatar_split_clause,[],[f214,f209,f219])).
% 0.21/0.51  fof(f209,plain,(
% 0.21/0.51    spl10_18 <=> r2_hidden(sK7(sK4,sK2,sK3),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    ~v1_xboole_0(sK2) | ~spl10_18),
% 0.21/0.51    inference(resolution,[],[f211,f39])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | ~spl10_18),
% 0.21/0.51    inference(avatar_component_clause,[],[f209])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl10_18 | ~spl10_5 | ~spl10_9),
% 0.21/0.51    inference(avatar_split_clause,[],[f202,f133,f88,f209])).
% 0.21/0.51  fof(f202,plain,(
% 0.21/0.51    r2_hidden(sK7(sK4,sK2,sK3),sK2) | (~spl10_5 | ~spl10_9)),
% 0.21/0.51    inference(resolution,[],[f95,f135])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X4,X5] : (~r2_hidden(X4,k9_relat_1(sK3,X5)) | r2_hidden(sK7(X4,X5,sK3),X5)) ) | ~spl10_5),
% 0.21/0.51    inference(resolution,[],[f90,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(sK7(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f188,plain,(
% 0.21/0.51    ~spl10_16 | ~spl10_3 | spl10_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f183,f98,f70,f185])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    spl10_6 <=> v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.51  fof(f183,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1) | (~spl10_3 | spl10_6)),
% 0.21/0.51    inference(resolution,[],[f182,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X0] : (m1_subset_1(k9_relat_1(sK3,X0),k1_zfmisc_1(sK1))) ) | ~spl10_3),
% 0.21/0.51    inference(superposition,[],[f84,f85])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k9_relat_1(sK3,sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | (~spl10_3 | spl10_6)),
% 0.21/0.51    inference(forward_demodulation,[],[f103,f85])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k7_relset_1(sK0,sK1,sK3,sK2),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | spl10_6),
% 0.21/0.51    inference(resolution,[],[f100,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ~v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2)) | spl10_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f98])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    ~spl10_14 | ~spl10_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f161,f138,f164])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    spl10_10 <=> r2_hidden(sK8(sK0,sK3),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    ~v1_xboole_0(sK0) | ~spl10_10),
% 0.21/0.51    inference(resolution,[],[f140,f39])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f138])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    spl10_10 | spl10_11 | ~spl10_3 | ~spl10_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f131,f110,f70,f142,f138])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    spl10_11 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_11])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl10_7 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    sK0 = k1_relat_1(sK3) | r2_hidden(sK8(sK0,sK3),sK0) | (~spl10_3 | ~spl10_7)),
% 0.21/0.51    inference(forward_demodulation,[],[f81,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    sK0 = k1_relset_1(sK0,sK1,sK3) | r2_hidden(sK8(sK0,sK3),sK0) | ~spl10_3),
% 0.21/0.51    inference(resolution,[],[f72,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k1_relset_1(X1,X0,X2) = X1 | r2_hidden(sK8(X1,X2),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X3,X4),X2) | ~r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X3,X4),X2) & r2_hidden(X3,X1)) <=> k1_relset_1(X1,X0,X2) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relset_1)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    spl10_9 | ~spl10_3 | ~spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f116,f75,f70,f133])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    spl10_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl10_3 | ~spl10_4)),
% 0.21/0.51    inference(superposition,[],[f77,f85])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f75])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl10_7 | ~spl10_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f80,f70,f110])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl10_3),
% 0.21/0.51    inference(resolution,[],[f72,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ~spl10_6 | ~spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f92,f75,f98])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ~v1_xboole_0(k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl10_4),
% 0.21/0.51    inference(resolution,[],[f77,f39])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl10_5 | ~spl10_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f79,f70,f88])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v1_relat_1(sK3) | ~spl10_3),
% 0.21/0.51    inference(resolution,[],[f72,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  % (12779)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl10_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f75])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl10_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f32,f70])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl10_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f57])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    v1_funct_1(sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (12762)------------------------------
% 0.21/0.51  % (12762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12762)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (12762)Memory used [KB]: 11001
% 0.21/0.51  % (12762)Time elapsed: 0.093 s
% 0.21/0.51  % (12762)------------------------------
% 0.21/0.51  % (12762)------------------------------
% 0.21/0.52  % (12758)Success in time 0.157 s
%------------------------------------------------------------------------------
