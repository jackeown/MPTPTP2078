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
% DateTime   : Thu Dec  3 13:01:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 266 expanded)
%              Number of leaves         :   39 ( 115 expanded)
%              Depth                    :   10
%              Number of atoms          :  451 ( 945 expanded)
%              Number of equality atoms :  104 ( 199 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f750,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f90,f95,f100,f132,f137,f166,f181,f197,f202,f269,f275,f334,f340,f461,f467,f536,f547,f550,f633,f634,f643,f645,f749])).

fof(f749,plain,
    ( spl5_63
    | ~ spl5_52
    | ~ spl5_7
    | ~ spl5_54
    | ~ spl5_3
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_62 ),
    inference(avatar_split_clause,[],[f748,f626,f272,f266,f77,f538,f97,f530,f630])).

fof(f630,plain,
    ( spl5_63
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f530,plain,
    ( spl5_52
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f97,plain,
    ( spl5_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f538,plain,
    ( spl5_54
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f77,plain,
    ( spl5_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f266,plain,
    ( spl5_25
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f272,plain,
    ( spl5_26
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f626,plain,
    ( spl5_62
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f748,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_62 ),
    inference(trivial_inequality_removal,[],[f747])).

fof(f747,plain,
    ( sK0 != sK0
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl5_25
    | ~ spl5_26
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f746,f268])).

fof(f268,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f266])).

fof(f746,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl5_26
    | ~ spl5_62 ),
    inference(forward_demodulation,[],[f745,f274])).

fof(f274,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f272])).

fof(f745,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl5_62 ),
    inference(trivial_inequality_removal,[],[f744])).

fof(f744,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = sK3
    | ~ spl5_62 ),
    inference(superposition,[],[f37,f628])).

fof(f628,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f626])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f645,plain,
    ( spl5_13
    | ~ spl5_14
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f507,f129,f152,f148])).

fof(f148,plain,
    ( spl5_13
  <=> sK2 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f152,plain,
    ( spl5_14
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f129,plain,
    ( spl5_11
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f507,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_11 ),
    inference(resolution,[],[f131,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f131,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f643,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f634,plain,
    ( sK2 != k2_zfmisc_1(sK0,sK1)
    | sK3 != k2_zfmisc_1(sK0,sK1)
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f633,plain,
    ( spl5_62
    | ~ spl5_54
    | ~ spl5_7
    | spl5_63
    | ~ spl5_26
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f624,f534,f272,f630,f97,f538,f626])).

fof(f534,plain,
    ( spl5_53
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f624,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl5_26
    | ~ spl5_53 ),
    inference(trivial_inequality_removal,[],[f623])).

fof(f623,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl5_26
    | ~ spl5_53 ),
    inference(superposition,[],[f557,f274])).

fof(f557,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0)) )
    | ~ spl5_53 ),
    inference(resolution,[],[f535,f26])).

fof(f26,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f535,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f534])).

fof(f550,plain,
    ( ~ spl5_5
    | spl5_54 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl5_5
    | spl5_54 ),
    inference(unit_resulting_resolution,[],[f38,f89,f540,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f540,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_54 ),
    inference(avatar_component_clause,[],[f538])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f547,plain,
    ( ~ spl5_1
    | spl5_52 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl5_1
    | spl5_52 ),
    inference(unit_resulting_resolution,[],[f38,f69,f532,f35])).

fof(f532,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_52 ),
    inference(avatar_component_clause,[],[f530])).

fof(f69,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f536,plain,
    ( ~ spl5_52
    | ~ spl5_3
    | spl5_53
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f527,f266,f534,f77,f530])).

fof(f527,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | sK2 = X0 )
    | ~ spl5_25 ),
    inference(superposition,[],[f36,f268])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f467,plain,(
    spl5_35 ),
    inference(avatar_contradiction_clause,[],[f463])).

fof(f463,plain,
    ( $false
    | spl5_35 ),
    inference(unit_resulting_resolution,[],[f34,f339,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f339,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_35 ),
    inference(avatar_component_clause,[],[f337])).

fof(f337,plain,
    ( spl5_35
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f461,plain,(
    spl5_34 ),
    inference(avatar_contradiction_clause,[],[f457])).

fof(f457,plain,
    ( $false
    | spl5_34 ),
    inference(unit_resulting_resolution,[],[f34,f333,f43])).

fof(f333,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_34 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl5_34
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f340,plain,
    ( ~ spl5_35
    | spl5_16
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f335,f262,f161,f337])).

fof(f161,plain,
    ( spl5_16
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f262,plain,
    ( spl5_24
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f335,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl5_16
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f285,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f285,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3)
    | spl5_16
    | ~ spl5_24 ),
    inference(backward_demodulation,[],[f163,f264])).

fof(f264,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f262])).

fof(f163,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f334,plain,
    ( ~ spl5_34
    | spl5_14
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f329,f262,f152,f331])).

fof(f329,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_14
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f284,f58])).

fof(f284,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | spl5_14
    | ~ spl5_24 ),
    inference(backward_demodulation,[],[f154,f264])).

fof(f154,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f152])).

fof(f275,plain,
    ( ~ spl5_6
    | spl5_24
    | spl5_26
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f270,f199,f87,f272,f262,f92])).

fof(f92,plain,
    ( spl5_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f199,plain,
    ( spl5_20
  <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f270,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f255,f201])).

fof(f201,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f199])).

fof(f255,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f53,f89])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f269,plain,
    ( ~ spl5_2
    | spl5_24
    | spl5_25
    | ~ spl5_1
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f260,f194,f67,f266,f262,f72])).

fof(f72,plain,
    ( spl5_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f194,plain,
    ( spl5_19
  <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f260,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_1
    | ~ spl5_19 ),
    inference(forward_demodulation,[],[f254,f196])).

fof(f196,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f254,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f53,f69])).

fof(f202,plain,
    ( spl5_20
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f188,f87,f199])).

fof(f188,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)
    | ~ spl5_5 ),
    inference(resolution,[],[f47,f89])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f197,plain,
    ( spl5_19
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f187,f67,f194])).

fof(f187,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f47,f69])).

fof(f181,plain,
    ( spl5_17
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f171,f67,f178])).

fof(f178,plain,
    ( spl5_17
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f171,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f65,f69])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f166,plain,
    ( spl5_15
    | ~ spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f145,f134,f161,f157])).

fof(f157,plain,
    ( spl5_15
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f134,plain,
    ( spl5_12
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f145,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f41,f136])).

fof(f136,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f137,plain,
    ( spl5_12
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f125,f87,f134])).

fof(f125,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_5 ),
    inference(resolution,[],[f43,f89])).

fof(f132,plain,
    ( spl5_11
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f124,f67,f129])).

fof(f124,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f43,f69])).

fof(f100,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f27,f97])).

fof(f27,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f95,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f28,f92])).

fof(f28,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f90,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f29,f87])).

fof(f29,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f85,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f30,f82])).

fof(f82,plain,
    ( spl5_4
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f30,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f75,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f32,f72])).

fof(f32,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f70,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f33,f67])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:17:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (15752)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.46  % (15760)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.48  % (15752)Refutation not found, incomplete strategy% (15752)------------------------------
% 0.21/0.48  % (15752)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15752)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (15752)Memory used [KB]: 1663
% 0.21/0.48  % (15752)Time elapsed: 0.067 s
% 0.21/0.48  % (15752)------------------------------
% 0.21/0.48  % (15752)------------------------------
% 0.21/0.48  % (15760)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f750,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f90,f95,f100,f132,f137,f166,f181,f197,f202,f269,f275,f334,f340,f461,f467,f536,f547,f550,f633,f634,f643,f645,f749])).
% 0.21/0.48  fof(f749,plain,(
% 0.21/0.48    spl5_63 | ~spl5_52 | ~spl5_7 | ~spl5_54 | ~spl5_3 | ~spl5_25 | ~spl5_26 | ~spl5_62),
% 0.21/0.48    inference(avatar_split_clause,[],[f748,f626,f272,f266,f77,f538,f97,f530,f630])).
% 0.21/0.48  fof(f630,plain,(
% 0.21/0.48    spl5_63 <=> sK2 = sK3),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 0.21/0.48  fof(f530,plain,(
% 0.21/0.48    spl5_52 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl5_7 <=> v1_funct_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.48  fof(f538,plain,(
% 0.21/0.48    spl5_54 <=> v1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    spl5_3 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    spl5_25 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    spl5_26 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.48  fof(f626,plain,(
% 0.21/0.48    spl5_62 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.21/0.48  fof(f748,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | sK2 = sK3 | (~spl5_25 | ~spl5_26 | ~spl5_62)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f747])).
% 0.21/0.48  fof(f747,plain,(
% 0.21/0.48    sK0 != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | sK2 = sK3 | (~spl5_25 | ~spl5_26 | ~spl5_62)),
% 0.21/0.48    inference(forward_demodulation,[],[f746,f268])).
% 0.21/0.48  fof(f268,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f266])).
% 0.21/0.48  fof(f746,plain,(
% 0.21/0.48    sK0 != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | sK2 = sK3 | (~spl5_26 | ~spl5_62)),
% 0.21/0.48    inference(forward_demodulation,[],[f745,f274])).
% 0.21/0.48  fof(f274,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl5_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f272])).
% 0.21/0.48  fof(f745,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK2 = sK3 | ~spl5_62),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f744])).
% 0.21/0.48  fof(f744,plain,(
% 0.21/0.48    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK2 = sK3 | ~spl5_62),
% 0.21/0.48    inference(superposition,[],[f37,f628])).
% 0.21/0.48  fof(f628,plain,(
% 0.21/0.48    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl5_62),
% 0.21/0.48    inference(avatar_component_clause,[],[f626])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.48  fof(f645,plain,(
% 0.21/0.48    spl5_13 | ~spl5_14 | ~spl5_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f507,f129,f152,f148])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl5_13 <=> sK2 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl5_14 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    spl5_11 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.48  fof(f507,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1) | ~spl5_11),
% 0.21/0.48    inference(resolution,[],[f131,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl5_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f129])).
% 0.21/0.48  fof(f643,plain,(
% 0.21/0.48    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f634,plain,(
% 0.21/0.48    sK2 != k2_zfmisc_1(sK0,sK1) | sK3 != k2_zfmisc_1(sK0,sK1) | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.48  fof(f633,plain,(
% 0.21/0.48    spl5_62 | ~spl5_54 | ~spl5_7 | spl5_63 | ~spl5_26 | ~spl5_53),
% 0.21/0.48    inference(avatar_split_clause,[],[f624,f534,f272,f630,f97,f538,f626])).
% 0.21/0.48  fof(f534,plain,(
% 0.21/0.48    spl5_53 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.21/0.48  fof(f624,plain,(
% 0.21/0.48    sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl5_26 | ~spl5_53)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f623])).
% 0.21/0.48  fof(f623,plain,(
% 0.21/0.48    sK0 != sK0 | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl5_26 | ~spl5_53)),
% 0.21/0.48    inference(superposition,[],[f557,f274])).
% 0.21/0.48  fof(f557,plain,(
% 0.21/0.48    ( ! [X0] : (k1_relat_1(X0) != sK0 | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(sK2,sK4(sK2,X0)) = k1_funct_1(sK3,sK4(sK2,X0))) ) | ~spl5_53),
% 0.21/0.48    inference(resolution,[],[f535,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.48  fof(f535,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_53),
% 0.21/0.48    inference(avatar_component_clause,[],[f534])).
% 0.21/0.48  fof(f550,plain,(
% 0.21/0.48    ~spl5_5 | spl5_54),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f548])).
% 0.21/0.48  fof(f548,plain,(
% 0.21/0.48    $false | (~spl5_5 | spl5_54)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f38,f89,f540,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f540,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | spl5_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f538])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f547,plain,(
% 0.21/0.48    ~spl5_1 | spl5_52),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f545])).
% 0.21/0.48  fof(f545,plain,(
% 0.21/0.48    $false | (~spl5_1 | spl5_52)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f38,f69,f532,f35])).
% 0.21/0.48  fof(f532,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl5_52),
% 0.21/0.48    inference(avatar_component_clause,[],[f530])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    spl5_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f536,plain,(
% 0.21/0.48    ~spl5_52 | ~spl5_3 | spl5_53 | ~spl5_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f527,f266,f534,f77,f530])).
% 0.21/0.48  fof(f527,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | sK2 = X0) ) | ~spl5_25),
% 0.21/0.48    inference(superposition,[],[f36,f268])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f467,plain,(
% 0.21/0.48    spl5_35),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f463])).
% 0.21/0.48  fof(f463,plain,(
% 0.21/0.48    $false | spl5_35),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f34,f339,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f339,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK3) | spl5_35),
% 0.21/0.48    inference(avatar_component_clause,[],[f337])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    spl5_35 <=> r1_tarski(k1_xboole_0,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f461,plain,(
% 0.21/0.48    spl5_34),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f457])).
% 0.21/0.48  fof(f457,plain,(
% 0.21/0.48    $false | spl5_34),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f34,f333,f43])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK2) | spl5_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f331])).
% 0.21/0.48  fof(f331,plain,(
% 0.21/0.48    spl5_34 <=> r1_tarski(k1_xboole_0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.48  fof(f340,plain,(
% 0.21/0.48    ~spl5_35 | spl5_16 | ~spl5_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f335,f262,f161,f337])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    spl5_16 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.48  fof(f262,plain,(
% 0.21/0.48    spl5_24 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK3) | (spl5_16 | ~spl5_24)),
% 0.21/0.48    inference(forward_demodulation,[],[f285,f58])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK3) | (spl5_16 | ~spl5_24)),
% 0.21/0.48    inference(backward_demodulation,[],[f163,f264])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl5_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f262])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl5_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f161])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    ~spl5_34 | spl5_14 | ~spl5_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f329,f262,f152,f331])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    ~r1_tarski(k1_xboole_0,sK2) | (spl5_14 | ~spl5_24)),
% 0.21/0.48    inference(forward_demodulation,[],[f284,f58])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | (spl5_14 | ~spl5_24)),
% 0.21/0.48    inference(backward_demodulation,[],[f154,f264])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | spl5_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    ~spl5_6 | spl5_24 | spl5_26 | ~spl5_5 | ~spl5_20),
% 0.21/0.48    inference(avatar_split_clause,[],[f270,f199,f87,f272,f262,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl5_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    spl5_20 <=> k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl5_5 | ~spl5_20)),
% 0.21/0.48    inference(forward_demodulation,[],[f255,f201])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl5_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f199])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f53,f89])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    ~spl5_2 | spl5_24 | spl5_25 | ~spl5_1 | ~spl5_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f260,f194,f67,f266,f262,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl5_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f194,plain,(
% 0.21/0.48    spl5_19 <=> k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | (~spl5_1 | ~spl5_19)),
% 0.21/0.48    inference(forward_demodulation,[],[f254,f196])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl5_19),
% 0.21/0.48    inference(avatar_component_clause,[],[f194])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f53,f69])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    spl5_20 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f188,f87,f199])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f47,f89])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl5_19 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f187,f67,f194])).
% 0.21/0.48  fof(f187,plain,(
% 0.21/0.48    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f47,f69])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl5_17 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f171,f67,f178])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    spl5_17 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f65,f69])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.21/0.48    inference(condensation,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.21/0.48  fof(f166,plain,(
% 0.21/0.48    spl5_15 | ~spl5_16 | ~spl5_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f145,f134,f161,f157])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    spl5_15 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl5_12 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | sK3 = k2_zfmisc_1(sK0,sK1) | ~spl5_12),
% 0.21/0.48    inference(resolution,[],[f41,f136])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl5_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f134])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl5_12 | ~spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f125,f87,f134])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl5_5),
% 0.21/0.48    inference(resolution,[],[f43,f89])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl5_11 | ~spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f124,f67,f129])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl5_1),
% 0.21/0.48    inference(resolution,[],[f43,f69])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl5_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f27,f97])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f92])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f87])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f82])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl5_4 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f77])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f72])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f67])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (15760)------------------------------
% 0.21/0.48  % (15760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (15760)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (15760)Memory used [KB]: 6652
% 0.21/0.48  % (15760)Time elapsed: 0.063 s
% 0.21/0.48  % (15760)------------------------------
% 0.21/0.48  % (15760)------------------------------
% 0.21/0.49  % (15744)Success in time 0.128 s
%------------------------------------------------------------------------------
