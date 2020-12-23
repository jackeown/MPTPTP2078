%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 331 expanded)
%              Number of leaves         :   44 ( 149 expanded)
%              Depth                    :   10
%              Number of atoms          :  601 (1286 expanded)
%              Number of equality atoms :   83 ( 110 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f136,f192,f283,f507,f525,f539,f640,f648,f1085,f1136,f1204,f1251,f1385,f1403,f1408,f1427,f1433,f1603,f1659])).

fof(f1659,plain,
    ( ~ spl11_52
    | ~ spl11_99 ),
    inference(avatar_contradiction_clause,[],[f1658])).

fof(f1658,plain,
    ( $false
    | ~ spl11_52
    | ~ spl11_99 ),
    inference(subsumption_resolution,[],[f1657,f137])).

fof(f137,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f69,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1657,plain,
    ( r2_hidden(sK10(sK6,k1_xboole_0,sK8),k1_xboole_0)
    | ~ spl11_52
    | ~ spl11_99 ),
    inference(forward_demodulation,[],[f1199,f646])).

fof(f646,plain,
    ( k1_xboole_0 = sK7
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl11_52
  <=> k1_xboole_0 = sK7 ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f1199,plain,
    ( r2_hidden(sK10(sK6,sK7,sK8),sK7)
    | ~ spl11_99 ),
    inference(avatar_component_clause,[],[f1197])).

fof(f1197,plain,
    ( spl11_99
  <=> r2_hidden(sK10(sK6,sK7,sK8),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).

fof(f1603,plain,
    ( ~ spl11_52
    | spl11_107 ),
    inference(avatar_contradiction_clause,[],[f1602])).

fof(f1602,plain,
    ( $false
    | ~ spl11_52
    | spl11_107 ),
    inference(subsumption_resolution,[],[f1588,f69])).

fof(f1588,plain,
    ( ~ r1_tarski(k1_xboole_0,sK5)
    | ~ spl11_52
    | spl11_107 ),
    inference(backward_demodulation,[],[f1250,f646])).

fof(f1250,plain,
    ( ~ r1_tarski(sK7,sK5)
    | spl11_107 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f1248,plain,
    ( spl11_107
  <=> r1_tarski(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).

fof(f1433,plain,
    ( spl11_94
    | ~ spl11_124
    | ~ spl11_125 ),
    inference(avatar_split_clause,[],[f1432,f1405,f1400,f1133])).

fof(f1133,plain,
    ( spl11_94
  <=> r2_hidden(k1_funct_1(sK8,sK9(sK6,sK5,sK8)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f1400,plain,
    ( spl11_124
  <=> k1_funct_1(sK8,sK9(sK6,sK5,sK8)) = k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_124])])).

fof(f1405,plain,
    ( spl11_125
  <=> r2_hidden(k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).

fof(f1432,plain,
    ( r2_hidden(k1_funct_1(sK8,sK9(sK6,sK5,sK8)),sK5)
    | ~ spl11_124
    | ~ spl11_125 ),
    inference(backward_demodulation,[],[f1407,f1402])).

fof(f1402,plain,
    ( k1_funct_1(sK8,sK9(sK6,sK5,sK8)) = k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8))
    | ~ spl11_124 ),
    inference(avatar_component_clause,[],[f1400])).

fof(f1407,plain,
    ( r2_hidden(k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)),sK5)
    | ~ spl11_125 ),
    inference(avatar_component_clause,[],[f1405])).

fof(f1427,plain,
    ( spl11_38
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f981,f113,f484])).

fof(f484,plain,
    ( spl11_38
  <=> k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f113,plain,
    ( spl11_2
  <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f981,plain,
    ( k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f115,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f115,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f1408,plain,
    ( spl11_125
    | ~ spl11_121 ),
    inference(avatar_split_clause,[],[f1397,f1382,f1405])).

fof(f1382,plain,
    ( spl11_121
  <=> m1_subset_1(sK9(sK6,sK5,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).

fof(f1397,plain,
    ( r2_hidden(k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)),sK5)
    | ~ spl11_121 ),
    inference(unit_resulting_resolution,[],[f1384,f67])).

fof(f67,plain,(
    ! [X4] :
      ( r2_hidden(k3_funct_2(sK6,sK7,sK8,X4),sK5)
      | ~ m1_subset_1(X4,sK6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5)
    & ! [X4] :
        ( r2_hidden(k3_funct_2(sK6,sK7,sK8,X4),sK5)
        | ~ m1_subset_1(X4,sK6) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8)
    & ~ v1_xboole_0(sK7)
    & ~ v1_xboole_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f18,f46,f45,f44])).

fof(f44,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
                & ! [X4] :
                    ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                    | ~ m1_subset_1(X4,X1) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(sK6,X2,X3),sK5)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(sK6,X2,X3,X4),sK5)
                  | ~ m1_subset_1(X4,sK6) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
              & v1_funct_2(X3,sK6,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_tarski(k2_relset_1(sK6,X2,X3),sK5)
            & ! [X4] :
                ( r2_hidden(k3_funct_2(sK6,X2,X3,X4),sK5)
                | ~ m1_subset_1(X4,sK6) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,X2)))
            & v1_funct_2(X3,sK6,X2)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ~ r1_tarski(k2_relset_1(sK6,sK7,X3),sK5)
          & ! [X4] :
              ( r2_hidden(k3_funct_2(sK6,sK7,X3,X4),sK5)
              | ~ m1_subset_1(X4,sK6) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
          & v1_funct_2(X3,sK6,sK7)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ~ r1_tarski(k2_relset_1(sK6,sK7,X3),sK5)
        & ! [X4] :
            ( r2_hidden(k3_funct_2(sK6,sK7,X3,X4),sK5)
            | ~ m1_subset_1(X4,sK6) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
        & v1_funct_2(X3,sK6,sK7)
        & v1_funct_1(X3) )
   => ( ~ r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5)
      & ! [X4] :
          ( r2_hidden(k3_funct_2(sK6,sK7,sK8,X4),sK5)
          | ~ m1_subset_1(X4,sK6) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK8,sK6,sK7)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).

fof(f1384,plain,
    ( m1_subset_1(sK9(sK6,sK5,sK8),sK6)
    | ~ spl11_121 ),
    inference(avatar_component_clause,[],[f1382])).

fof(f1403,plain,
    ( spl11_124
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_6
    | ~ spl11_121 ),
    inference(avatar_split_clause,[],[f1398,f1382,f133,f123,f118,f113,f1400])).

fof(f118,plain,
    ( spl11_3
  <=> v1_funct_2(sK8,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f123,plain,
    ( spl11_4
  <=> v1_funct_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f133,plain,
    ( spl11_6
  <=> v1_xboole_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1398,plain,
    ( k1_funct_1(sK8,sK9(sK6,sK5,sK8)) = k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8))
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | spl11_6
    | ~ spl11_121 ),
    inference(unit_resulting_resolution,[],[f135,f125,f120,f115,f1384,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f120,plain,
    ( v1_funct_2(sK8,sK6,sK7)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( v1_funct_1(sK8)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f135,plain,
    ( ~ v1_xboole_0(sK6)
    | spl11_6 ),
    inference(avatar_component_clause,[],[f133])).

fof(f1385,plain,
    ( spl11_121
    | ~ spl11_89 ),
    inference(avatar_split_clause,[],[f1379,f1082,f1382])).

fof(f1082,plain,
    ( spl11_89
  <=> r2_hidden(sK9(sK6,sK5,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).

fof(f1379,plain,
    ( m1_subset_1(sK9(sK6,sK5,sK8),sK6)
    | ~ spl11_89 ),
    inference(unit_resulting_resolution,[],[f1084,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f1084,plain,
    ( r2_hidden(sK9(sK6,sK5,sK8),sK6)
    | ~ spl11_89 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1251,plain,
    ( ~ spl11_107
    | spl11_43
    | ~ spl11_100 ),
    inference(avatar_split_clause,[],[f1211,f1201,f522,f1248])).

fof(f522,plain,
    ( spl11_43
  <=> r1_tarski(k2_relat_1(sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).

fof(f1201,plain,
    ( spl11_100
  <=> sK7 = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).

fof(f1211,plain,
    ( ~ r1_tarski(sK7,sK5)
    | spl11_43
    | ~ spl11_100 ),
    inference(backward_demodulation,[],[f524,f1203])).

fof(f1203,plain,
    ( sK7 = k2_relat_1(sK8)
    | ~ spl11_100 ),
    inference(avatar_component_clause,[],[f1201])).

fof(f524,plain,
    ( ~ r1_tarski(k2_relat_1(sK8),sK5)
    | spl11_43 ),
    inference(avatar_component_clause,[],[f522])).

fof(f1204,plain,
    ( spl11_99
    | spl11_100
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f1195,f504,f123,f118,f113,f1201,f1197])).

fof(f504,plain,
    ( spl11_40
  <=> k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f1195,plain,
    ( sK7 = k2_relat_1(sK8)
    | r2_hidden(sK10(sK6,sK7,sK8),sK7)
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_40 ),
    inference(forward_demodulation,[],[f1194,f506])).

fof(f506,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8)
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f504])).

fof(f1194,plain,
    ( r2_hidden(sK10(sK6,sK7,sK8),sK7)
    | sK7 = k2_relset_1(sK6,sK7,sK8)
    | ~ spl11_2
    | ~ spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f1193,f125])).

fof(f1193,plain,
    ( r2_hidden(sK10(sK6,sK7,sK8),sK7)
    | sK7 = k2_relset_1(sK6,sK7,sK8)
    | ~ v1_funct_1(sK8)
    | ~ spl11_2
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f1188,f120])).

fof(f1188,plain,
    ( r2_hidden(sK10(sK6,sK7,sK8),sK7)
    | sK7 = k2_relset_1(sK6,sK7,sK8)
    | ~ v1_funct_2(sK8,sK6,sK7)
    | ~ v1_funct_1(sK8)
    | ~ spl11_2 ),
    inference(resolution,[],[f98,f115])).

% (22177)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_hidden(sK10(X0,X1,X2),X1)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ( ! [X4] :
            ( k1_funct_1(X2,X4) != sK10(X0,X1,X2)
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(sK10(X0,X1,X2),X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f60])).

fof(f60,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) != X3
              | ~ r2_hidden(X4,X0) )
          & r2_hidden(X3,X1) )
     => ( ! [X4] :
            ( k1_funct_1(X2,X4) != sK10(X0,X1,X2)
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(sK10(X0,X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) != X3
              | ~ r2_hidden(X4,X0) )
          & r2_hidden(X3,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X2,X4) != X3
              | ~ r2_hidden(X4,X0) )
          & r2_hidden(X3,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

fof(f1136,plain,
    ( ~ spl11_94
    | ~ spl11_4
    | ~ spl11_12
    | spl11_44
    | ~ spl11_51 ),
    inference(avatar_split_clause,[],[f1131,f634,f534,f188,f123,f1133])).

fof(f188,plain,
    ( spl11_12
  <=> v1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f534,plain,
    ( spl11_44
  <=> v5_relat_1(sK8,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f634,plain,
    ( spl11_51
  <=> sK6 = k1_relat_1(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).

fof(f1131,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK9(sK6,sK5,sK8)),sK5)
    | ~ spl11_4
    | ~ spl11_12
    | spl11_44
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f1128,f636])).

fof(f636,plain,
    ( sK6 = k1_relat_1(sK8)
    | ~ spl11_51 ),
    inference(avatar_component_clause,[],[f634])).

fof(f1128,plain,
    ( ~ r2_hidden(k1_funct_1(sK8,sK9(k1_relat_1(sK8),sK5,sK8)),sK5)
    | ~ spl11_4
    | ~ spl11_12
    | spl11_44 ),
    inference(unit_resulting_resolution,[],[f190,f125,f554,f105])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1)
      | sP4(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1)
        & r2_hidden(sK9(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( sP4(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f31,f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP4(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).

fof(f554,plain,
    ( ! [X0] : ~ sP4(sK5,X0,sK8)
    | spl11_44 ),
    inference(unit_resulting_resolution,[],[f541,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP4(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f541,plain,
    ( ! [X0] : ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))
    | spl11_44 ),
    inference(unit_resulting_resolution,[],[f536,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f536,plain,
    ( ~ v5_relat_1(sK8,sK5)
    | spl11_44 ),
    inference(avatar_component_clause,[],[f534])).

fof(f190,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f188])).

fof(f1085,plain,
    ( spl11_89
    | ~ spl11_4
    | ~ spl11_12
    | spl11_44
    | ~ spl11_51 ),
    inference(avatar_split_clause,[],[f1080,f634,f534,f188,f123,f1082])).

fof(f1080,plain,
    ( r2_hidden(sK9(sK6,sK5,sK8),sK6)
    | ~ spl11_4
    | ~ spl11_12
    | spl11_44
    | ~ spl11_51 ),
    inference(forward_demodulation,[],[f1070,f636])).

fof(f1070,plain,
    ( r2_hidden(sK9(k1_relat_1(sK8),sK5,sK8),k1_relat_1(sK8))
    | ~ spl11_4
    | ~ spl11_12
    | spl11_44 ),
    inference(unit_resulting_resolution,[],[f190,f125,f554,f106])).

fof(f106,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP4(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X0,X2)
      | r2_hidden(sK9(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f648,plain,
    ( spl11_52
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f642,f630,f644])).

fof(f630,plain,
    ( spl11_50
  <=> sP1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f642,plain,
    ( k1_xboole_0 = sK7
    | ~ spl11_50 ),
    inference(resolution,[],[f632,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f632,plain,
    ( sP1(sK6,sK7)
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f630])).

fof(f640,plain,
    ( spl11_50
    | spl11_51
    | ~ spl11_3
    | ~ spl11_19
    | ~ spl11_38 ),
    inference(avatar_split_clause,[],[f639,f484,f279,f118,f634,f630])).

fof(f279,plain,
    ( spl11_19
  <=> sP2(sK6,sK8,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f639,plain,
    ( sK6 = k1_relat_1(sK8)
    | sP1(sK6,sK7)
    | ~ spl11_3
    | ~ spl11_19
    | ~ spl11_38 ),
    inference(subsumption_resolution,[],[f638,f281])).

fof(f281,plain,
    ( sP2(sK6,sK8,sK7)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f279])).

fof(f638,plain,
    ( sK6 = k1_relat_1(sK8)
    | sP1(sK6,sK7)
    | ~ sP2(sK6,sK8,sK7)
    | ~ spl11_3
    | ~ spl11_38 ),
    inference(subsumption_resolution,[],[f625,f120])).

fof(f625,plain,
    ( sK6 = k1_relat_1(sK8)
    | ~ v1_funct_2(sK8,sK6,sK7)
    | sP1(sK6,sK7)
    | ~ sP2(sK6,sK8,sK7)
    | ~ spl11_38 ),
    inference(superposition,[],[f486,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP1(X0,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP1(X0,X1)
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f486,plain,
    ( k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f484])).

fof(f539,plain,
    ( ~ spl11_44
    | ~ spl11_12
    | spl11_43 ),
    inference(avatar_split_clause,[],[f538,f522,f188,f534])).

fof(f538,plain,
    ( ~ v5_relat_1(sK8,sK5)
    | ~ spl11_12
    | spl11_43 ),
    inference(subsumption_resolution,[],[f532,f190])).

fof(f532,plain,
    ( ~ v5_relat_1(sK8,sK5)
    | ~ v1_relat_1(sK8)
    | spl11_43 ),
    inference(resolution,[],[f524,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f525,plain,
    ( ~ spl11_43
    | spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f520,f113,f108,f522])).

fof(f108,plain,
    ( spl11_1
  <=> r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f520,plain,
    ( ~ r1_tarski(k2_relat_1(sK8),sK5)
    | spl11_1
    | ~ spl11_2 ),
    inference(subsumption_resolution,[],[f497,f115])).

fof(f497,plain,
    ( ~ r1_tarski(k2_relat_1(sK8),sK5)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | spl11_1 ),
    inference(superposition,[],[f110,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f110,plain,
    ( ~ r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f507,plain,
    ( spl11_40
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f490,f113,f504])).

fof(f490,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8)
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f115,f82])).

fof(f283,plain,
    ( spl11_19
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f277,f113,f279])).

fof(f277,plain,
    ( sP2(sK6,sK8,sK7)
    | ~ spl11_2 ),
    inference(resolution,[],[f91,f115])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X2,X1,X0)
        & sP2(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f29,f40,f39,f38])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP3(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f192,plain,
    ( spl11_12
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f178,f113,f188])).

fof(f178,plain,
    ( v1_relat_1(sK8)
    | ~ spl11_2 ),
    inference(resolution,[],[f80,f115])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,(
    ~ spl11_6 ),
    inference(avatar_split_clause,[],[f62,f133])).

fof(f62,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f126,plain,(
    spl11_4 ),
    inference(avatar_split_clause,[],[f64,f123])).

fof(f64,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f121,plain,(
    spl11_3 ),
    inference(avatar_split_clause,[],[f65,f118])).

fof(f65,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,(
    spl11_2 ),
    inference(avatar_split_clause,[],[f66,f113])).

fof(f66,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f47])).

fof(f111,plain,(
    ~ spl11_1 ),
    inference(avatar_split_clause,[],[f68,f108])).

fof(f68,plain,(
    ~ r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (22172)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (22181)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (22168)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (22174)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (22184)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (22179)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.51  % (22167)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (22175)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (22165)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (22171)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.52  % (22181)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f1763,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f111,f116,f121,f126,f136,f192,f283,f507,f525,f539,f640,f648,f1085,f1136,f1204,f1251,f1385,f1403,f1408,f1427,f1433,f1603,f1659])).
% 0.21/0.52  fof(f1659,plain,(
% 0.21/0.52    ~spl11_52 | ~spl11_99),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1658])).
% 0.21/0.52  fof(f1658,plain,(
% 0.21/0.52    $false | (~spl11_52 | ~spl11_99)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1657,f137])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f69,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f1657,plain,(
% 0.21/0.52    r2_hidden(sK10(sK6,k1_xboole_0,sK8),k1_xboole_0) | (~spl11_52 | ~spl11_99)),
% 0.21/0.52    inference(forward_demodulation,[],[f1199,f646])).
% 0.21/0.52  fof(f646,plain,(
% 0.21/0.52    k1_xboole_0 = sK7 | ~spl11_52),
% 0.21/0.52    inference(avatar_component_clause,[],[f644])).
% 0.21/0.52  fof(f644,plain,(
% 0.21/0.52    spl11_52 <=> k1_xboole_0 = sK7),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).
% 0.21/0.52  fof(f1199,plain,(
% 0.21/0.52    r2_hidden(sK10(sK6,sK7,sK8),sK7) | ~spl11_99),
% 0.21/0.52    inference(avatar_component_clause,[],[f1197])).
% 0.21/0.52  fof(f1197,plain,(
% 0.21/0.52    spl11_99 <=> r2_hidden(sK10(sK6,sK7,sK8),sK7)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_99])])).
% 0.21/0.52  fof(f1603,plain,(
% 0.21/0.52    ~spl11_52 | spl11_107),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f1602])).
% 0.21/0.52  fof(f1602,plain,(
% 0.21/0.52    $false | (~spl11_52 | spl11_107)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1588,f69])).
% 0.21/0.52  fof(f1588,plain,(
% 0.21/0.52    ~r1_tarski(k1_xboole_0,sK5) | (~spl11_52 | spl11_107)),
% 0.21/0.52    inference(backward_demodulation,[],[f1250,f646])).
% 0.21/0.52  fof(f1250,plain,(
% 0.21/0.52    ~r1_tarski(sK7,sK5) | spl11_107),
% 0.21/0.52    inference(avatar_component_clause,[],[f1248])).
% 0.21/0.52  fof(f1248,plain,(
% 0.21/0.52    spl11_107 <=> r1_tarski(sK7,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_107])])).
% 0.21/0.52  fof(f1433,plain,(
% 0.21/0.52    spl11_94 | ~spl11_124 | ~spl11_125),
% 0.21/0.52    inference(avatar_split_clause,[],[f1432,f1405,f1400,f1133])).
% 0.21/0.52  fof(f1133,plain,(
% 0.21/0.52    spl11_94 <=> r2_hidden(k1_funct_1(sK8,sK9(sK6,sK5,sK8)),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).
% 0.21/0.52  fof(f1400,plain,(
% 0.21/0.52    spl11_124 <=> k1_funct_1(sK8,sK9(sK6,sK5,sK8)) = k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_124])])).
% 0.21/0.52  fof(f1405,plain,(
% 0.21/0.52    spl11_125 <=> r2_hidden(k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_125])])).
% 0.21/0.52  fof(f1432,plain,(
% 0.21/0.52    r2_hidden(k1_funct_1(sK8,sK9(sK6,sK5,sK8)),sK5) | (~spl11_124 | ~spl11_125)),
% 0.21/0.52    inference(backward_demodulation,[],[f1407,f1402])).
% 0.21/0.52  fof(f1402,plain,(
% 0.21/0.52    k1_funct_1(sK8,sK9(sK6,sK5,sK8)) = k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)) | ~spl11_124),
% 0.21/0.52    inference(avatar_component_clause,[],[f1400])).
% 0.21/0.52  fof(f1407,plain,(
% 0.21/0.52    r2_hidden(k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)),sK5) | ~spl11_125),
% 0.21/0.52    inference(avatar_component_clause,[],[f1405])).
% 0.21/0.52  fof(f1427,plain,(
% 0.21/0.52    spl11_38 | ~spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f981,f113,f484])).
% 0.21/0.52  fof(f484,plain,(
% 0.21/0.52    spl11_38 <=> k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    spl11_2 <=> m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.21/0.52  fof(f981,plain,(
% 0.21/0.52    k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8) | ~spl11_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f115,f81])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) | ~spl11_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f113])).
% 0.21/0.52  fof(f1408,plain,(
% 0.21/0.52    spl11_125 | ~spl11_121),
% 0.21/0.52    inference(avatar_split_clause,[],[f1397,f1382,f1405])).
% 0.21/0.52  fof(f1382,plain,(
% 0.21/0.52    spl11_121 <=> m1_subset_1(sK9(sK6,sK5,sK8),sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_121])])).
% 0.21/0.52  fof(f1397,plain,(
% 0.21/0.52    r2_hidden(k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)),sK5) | ~spl11_121),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f1384,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X4] : (r2_hidden(k3_funct_2(sK6,sK7,sK8,X4),sK5) | ~m1_subset_1(X4,sK6)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ((~r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5) & ! [X4] : (r2_hidden(k3_funct_2(sK6,sK7,sK8,X4),sK5) | ~m1_subset_1(X4,sK6)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)) & ~v1_xboole_0(sK7)) & ~v1_xboole_0(sK6)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f18,f46,f45,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK6,X2,X3),sK5) & ! [X4] : (r2_hidden(k3_funct_2(sK6,X2,X3,X4),sK5) | ~m1_subset_1(X4,sK6)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) & v1_funct_2(X3,sK6,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK6))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(sK6,X2,X3),sK5) & ! [X4] : (r2_hidden(k3_funct_2(sK6,X2,X3,X4),sK5) | ~m1_subset_1(X4,sK6)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,X2))) & v1_funct_2(X3,sK6,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) => (? [X3] : (~r1_tarski(k2_relset_1(sK6,sK7,X3),sK5) & ! [X4] : (r2_hidden(k3_funct_2(sK6,sK7,X3,X4),sK5) | ~m1_subset_1(X4,sK6)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(X3,sK6,sK7) & v1_funct_1(X3)) & ~v1_xboole_0(sK7))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ? [X3] : (~r1_tarski(k2_relset_1(sK6,sK7,X3),sK5) & ! [X4] : (r2_hidden(k3_funct_2(sK6,sK7,X3,X4),sK5) | ~m1_subset_1(X4,sK6)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(X3,sK6,sK7) & v1_funct_1(X3)) => (~r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5) & ! [X4] : (r2_hidden(k3_funct_2(sK6,sK7,sK8,X4),sK5) | ~m1_subset_1(X4,sK6)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f15])).
% 0.21/0.52  fof(f15,conjecture,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t191_funct_2)).
% 0.21/0.52  fof(f1384,plain,(
% 0.21/0.52    m1_subset_1(sK9(sK6,sK5,sK8),sK6) | ~spl11_121),
% 0.21/0.52    inference(avatar_component_clause,[],[f1382])).
% 0.21/0.52  fof(f1403,plain,(
% 0.21/0.52    spl11_124 | ~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_6 | ~spl11_121),
% 0.21/0.52    inference(avatar_split_clause,[],[f1398,f1382,f133,f123,f118,f113,f1400])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl11_3 <=> v1_funct_2(sK8,sK6,sK7)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    spl11_4 <=> v1_funct_1(sK8)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    spl11_6 <=> v1_xboole_0(sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 0.21/0.52  fof(f1398,plain,(
% 0.21/0.52    k1_funct_1(sK8,sK9(sK6,sK5,sK8)) = k3_funct_2(sK6,sK7,sK8,sK9(sK6,sK5,sK8)) | (~spl11_2 | ~spl11_3 | ~spl11_4 | spl11_6 | ~spl11_121)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f135,f125,f120,f115,f1384,f100])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    v1_funct_2(sK8,sK6,sK7) | ~spl11_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    v1_funct_1(sK8) | ~spl11_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f123])).
% 0.21/0.52  fof(f135,plain,(
% 0.21/0.52    ~v1_xboole_0(sK6) | spl11_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f133])).
% 0.21/0.52  fof(f1385,plain,(
% 0.21/0.52    spl11_121 | ~spl11_89),
% 0.21/0.52    inference(avatar_split_clause,[],[f1379,f1082,f1382])).
% 0.21/0.52  fof(f1082,plain,(
% 0.21/0.52    spl11_89 <=> r2_hidden(sK9(sK6,sK5,sK8),sK6)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_89])])).
% 0.21/0.52  fof(f1379,plain,(
% 0.21/0.52    m1_subset_1(sK9(sK6,sK5,sK8),sK6) | ~spl11_89),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f1084,f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.52  fof(f1084,plain,(
% 0.21/0.52    r2_hidden(sK9(sK6,sK5,sK8),sK6) | ~spl11_89),
% 0.21/0.52    inference(avatar_component_clause,[],[f1082])).
% 0.21/0.52  fof(f1251,plain,(
% 0.21/0.52    ~spl11_107 | spl11_43 | ~spl11_100),
% 0.21/0.52    inference(avatar_split_clause,[],[f1211,f1201,f522,f1248])).
% 0.21/0.52  fof(f522,plain,(
% 0.21/0.52    spl11_43 <=> r1_tarski(k2_relat_1(sK8),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_43])])).
% 0.21/0.52  fof(f1201,plain,(
% 0.21/0.52    spl11_100 <=> sK7 = k2_relat_1(sK8)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_100])])).
% 0.21/0.52  fof(f1211,plain,(
% 0.21/0.52    ~r1_tarski(sK7,sK5) | (spl11_43 | ~spl11_100)),
% 0.21/0.52    inference(backward_demodulation,[],[f524,f1203])).
% 0.21/0.52  fof(f1203,plain,(
% 0.21/0.52    sK7 = k2_relat_1(sK8) | ~spl11_100),
% 0.21/0.52    inference(avatar_component_clause,[],[f1201])).
% 0.21/0.52  fof(f524,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK8),sK5) | spl11_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f522])).
% 0.21/0.52  fof(f1204,plain,(
% 0.21/0.52    spl11_99 | spl11_100 | ~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f1195,f504,f123,f118,f113,f1201,f1197])).
% 0.21/0.52  fof(f504,plain,(
% 0.21/0.52    spl11_40 <=> k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).
% 0.21/0.52  fof(f1195,plain,(
% 0.21/0.52    sK7 = k2_relat_1(sK8) | r2_hidden(sK10(sK6,sK7,sK8),sK7) | (~spl11_2 | ~spl11_3 | ~spl11_4 | ~spl11_40)),
% 0.21/0.52    inference(forward_demodulation,[],[f1194,f506])).
% 0.21/0.52  fof(f506,plain,(
% 0.21/0.52    k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) | ~spl11_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f504])).
% 0.21/0.52  fof(f1194,plain,(
% 0.21/0.52    r2_hidden(sK10(sK6,sK7,sK8),sK7) | sK7 = k2_relset_1(sK6,sK7,sK8) | (~spl11_2 | ~spl11_3 | ~spl11_4)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1193,f125])).
% 0.21/0.52  fof(f1193,plain,(
% 0.21/0.52    r2_hidden(sK10(sK6,sK7,sK8),sK7) | sK7 = k2_relset_1(sK6,sK7,sK8) | ~v1_funct_1(sK8) | (~spl11_2 | ~spl11_3)),
% 0.21/0.52    inference(subsumption_resolution,[],[f1188,f120])).
% 0.21/0.52  fof(f1188,plain,(
% 0.21/0.52    r2_hidden(sK10(sK6,sK7,sK8),sK7) | sK7 = k2_relset_1(sK6,sK7,sK8) | ~v1_funct_2(sK8,sK6,sK7) | ~v1_funct_1(sK8) | ~spl11_2),
% 0.21/0.52    inference(resolution,[],[f98,f115])).
% 0.21/0.52  % (22177)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_hidden(sK10(X0,X1,X2),X1) | k2_relset_1(X0,X1,X2) = X1 | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = X1 | (! [X4] : (k1_funct_1(X2,X4) != sK10(X0,X1,X2) | ~r2_hidden(X4,X0)) & r2_hidden(sK10(X0,X1,X2),X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f33,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (! [X4] : (k1_funct_1(X2,X4) != X3 | ~r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => (! [X4] : (k1_funct_1(X2,X4) != sK10(X0,X1,X2) | ~r2_hidden(X4,X0)) & r2_hidden(sK10(X0,X1,X2),X1)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : (k1_funct_1(X2,X4) != X3 | ~r2_hidden(X4,X0)) & r2_hidden(X3,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.52    inference(flattening,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : (k1_funct_1(X2,X4) != X3 | ~r2_hidden(X4,X0)) & r2_hidden(X3,X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).
% 0.21/0.52  fof(f1136,plain,(
% 0.21/0.52    ~spl11_94 | ~spl11_4 | ~spl11_12 | spl11_44 | ~spl11_51),
% 0.21/0.52    inference(avatar_split_clause,[],[f1131,f634,f534,f188,f123,f1133])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    spl11_12 <=> v1_relat_1(sK8)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).
% 0.21/0.52  fof(f534,plain,(
% 0.21/0.52    spl11_44 <=> v5_relat_1(sK8,sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).
% 0.21/0.52  fof(f634,plain,(
% 0.21/0.52    spl11_51 <=> sK6 = k1_relat_1(sK8)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_51])])).
% 0.21/0.52  fof(f1131,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK8,sK9(sK6,sK5,sK8)),sK5) | (~spl11_4 | ~spl11_12 | spl11_44 | ~spl11_51)),
% 0.21/0.52    inference(forward_demodulation,[],[f1128,f636])).
% 0.21/0.52  fof(f636,plain,(
% 0.21/0.52    sK6 = k1_relat_1(sK8) | ~spl11_51),
% 0.21/0.52    inference(avatar_component_clause,[],[f634])).
% 0.21/0.52  fof(f1128,plain,(
% 0.21/0.52    ~r2_hidden(k1_funct_1(sK8,sK9(k1_relat_1(sK8),sK5,sK8)),sK5) | (~spl11_4 | ~spl11_12 | spl11_44)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f190,f125,f554,f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK9(k1_relat_1(X2),X1,X2)),X1) | sP4(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP4(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP4(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) & r2_hidden(sK9(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f43,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK9(X0,X1,X2)),X1) & r2_hidden(sK9(X0,X1,X2),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (sP4(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(definition_folding,[],[f31,f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP4(X1,X0,X2))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.21/0.52    inference(flattening,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_funct_2)).
% 0.21/0.52  fof(f554,plain,(
% 0.21/0.52    ( ! [X0] : (~sP4(sK5,X0,sK8)) ) | spl11_44),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f541,f95])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP4(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP4(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP4(X1,X0,X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f42])).
% 0.21/0.52  fof(f541,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,sK5)))) ) | spl11_44),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f536,f84])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f536,plain,(
% 0.21/0.52    ~v5_relat_1(sK8,sK5) | spl11_44),
% 0.21/0.52    inference(avatar_component_clause,[],[f534])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    v1_relat_1(sK8) | ~spl11_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f188])).
% 0.21/0.52  fof(f1085,plain,(
% 0.21/0.52    spl11_89 | ~spl11_4 | ~spl11_12 | spl11_44 | ~spl11_51),
% 0.21/0.52    inference(avatar_split_clause,[],[f1080,f634,f534,f188,f123,f1082])).
% 0.21/0.52  fof(f1080,plain,(
% 0.21/0.52    r2_hidden(sK9(sK6,sK5,sK8),sK6) | (~spl11_4 | ~spl11_12 | spl11_44 | ~spl11_51)),
% 0.21/0.52    inference(forward_demodulation,[],[f1070,f636])).
% 0.21/0.52  fof(f1070,plain,(
% 0.21/0.52    r2_hidden(sK9(k1_relat_1(sK8),sK5,sK8),k1_relat_1(sK8)) | (~spl11_4 | ~spl11_12 | spl11_44)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f190,f125,f554,f106])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r2_hidden(sK9(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP4(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(equality_resolution,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP4(X1,X0,X2) | r2_hidden(sK9(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f648,plain,(
% 0.21/0.52    spl11_52 | ~spl11_50),
% 0.21/0.52    inference(avatar_split_clause,[],[f642,f630,f644])).
% 0.21/0.52  fof(f630,plain,(
% 0.21/0.52    spl11_50 <=> sP1(sK6,sK7)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).
% 0.21/0.52  fof(f642,plain,(
% 0.21/0.52    k1_xboole_0 = sK7 | ~spl11_50),
% 0.21/0.52    inference(resolution,[],[f632,f89])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~sP1(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP1(X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f632,plain,(
% 0.21/0.52    sP1(sK6,sK7) | ~spl11_50),
% 0.21/0.52    inference(avatar_component_clause,[],[f630])).
% 0.21/0.52  fof(f640,plain,(
% 0.21/0.52    spl11_50 | spl11_51 | ~spl11_3 | ~spl11_19 | ~spl11_38),
% 0.21/0.52    inference(avatar_split_clause,[],[f639,f484,f279,f118,f634,f630])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    spl11_19 <=> sP2(sK6,sK8,sK7)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 0.21/0.52  fof(f639,plain,(
% 0.21/0.52    sK6 = k1_relat_1(sK8) | sP1(sK6,sK7) | (~spl11_3 | ~spl11_19 | ~spl11_38)),
% 0.21/0.52    inference(subsumption_resolution,[],[f638,f281])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    sP2(sK6,sK8,sK7) | ~spl11_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f279])).
% 0.21/0.52  fof(f638,plain,(
% 0.21/0.52    sK6 = k1_relat_1(sK8) | sP1(sK6,sK7) | ~sP2(sK6,sK8,sK7) | (~spl11_3 | ~spl11_38)),
% 0.21/0.52    inference(subsumption_resolution,[],[f625,f120])).
% 0.21/0.52  fof(f625,plain,(
% 0.21/0.52    sK6 = k1_relat_1(sK8) | ~v1_funct_2(sK8,sK6,sK7) | sP1(sK6,sK7) | ~sP2(sK6,sK8,sK7) | ~spl11_38),
% 0.21/0.52    inference(superposition,[],[f486,f87])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP1(X0,X2) | ~sP2(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP1(X0,X2) | ~sP2(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP1(X0,X1) | ~sP2(X0,X2,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.52  fof(f486,plain,(
% 0.21/0.52    k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8) | ~spl11_38),
% 0.21/0.52    inference(avatar_component_clause,[],[f484])).
% 0.21/0.52  fof(f539,plain,(
% 0.21/0.52    ~spl11_44 | ~spl11_12 | spl11_43),
% 0.21/0.52    inference(avatar_split_clause,[],[f538,f522,f188,f534])).
% 0.21/0.52  fof(f538,plain,(
% 0.21/0.52    ~v5_relat_1(sK8,sK5) | (~spl11_12 | spl11_43)),
% 0.21/0.52    inference(subsumption_resolution,[],[f532,f190])).
% 0.21/0.52  fof(f532,plain,(
% 0.21/0.52    ~v5_relat_1(sK8,sK5) | ~v1_relat_1(sK8) | spl11_43),
% 0.21/0.52    inference(resolution,[],[f524,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.52  fof(f525,plain,(
% 0.21/0.52    ~spl11_43 | spl11_1 | ~spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f520,f113,f108,f522])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl11_1 <=> r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.21/0.52  fof(f520,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK8),sK5) | (spl11_1 | ~spl11_2)),
% 0.21/0.52    inference(subsumption_resolution,[],[f497,f115])).
% 0.21/0.52  fof(f497,plain,(
% 0.21/0.52    ~r1_tarski(k2_relat_1(sK8),sK5) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) | spl11_1),
% 0.21/0.52    inference(superposition,[],[f110,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5) | spl11_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f507,plain,(
% 0.21/0.52    spl11_40 | ~spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f490,f113,f504])).
% 0.21/0.52  fof(f490,plain,(
% 0.21/0.52    k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) | ~spl11_2),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f115,f82])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    spl11_19 | ~spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f277,f113,f279])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    sP2(sK6,sK8,sK7) | ~spl11_2),
% 0.21/0.52    inference(resolution,[],[f91,f115])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X0,X2,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f41])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP3(X2,X1,X0) & sP2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(definition_folding,[],[f29,f40,f39,f38])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP3(X2,X1,X0))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f192,plain,(
% 0.21/0.52    spl11_12 | ~spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f178,f113,f188])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    v1_relat_1(sK8) | ~spl11_2),
% 0.21/0.52    inference(resolution,[],[f80,f115])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~spl11_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f133])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ~v1_xboole_0(sK6)),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl11_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f64,f123])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v1_funct_1(sK8)),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl11_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f65,f118])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v1_funct_2(sK8,sK6,sK7)),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl11_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f66,f113])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~spl11_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f108])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ~r1_tarski(k2_relset_1(sK6,sK7,sK8),sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (22181)------------------------------
% 0.21/0.52  % (22181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22181)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (22185)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (22176)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (22166)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (22180)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (22169)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.53  % (22186)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.53  % (22173)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.54  % (22170)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (22176)Refutation not found, incomplete strategy% (22176)------------------------------
% 0.21/0.54  % (22176)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22176)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22176)Memory used [KB]: 10746
% 0.21/0.54  % (22176)Time elapsed: 0.116 s
% 0.21/0.54  % (22176)------------------------------
% 0.21/0.54  % (22176)------------------------------
% 0.21/0.54  % (22186)Refutation not found, incomplete strategy% (22186)------------------------------
% 0.21/0.54  % (22186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22186)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22186)Memory used [KB]: 10618
% 0.21/0.54  % (22186)Time elapsed: 0.141 s
% 0.21/0.54  % (22186)------------------------------
% 0.21/0.54  % (22186)------------------------------
% 0.21/0.54  % (22181)Memory used [KB]: 11641
% 0.21/0.54  % (22181)Time elapsed: 0.118 s
% 0.21/0.54  % (22181)------------------------------
% 0.21/0.54  % (22181)------------------------------
% 0.21/0.54  % (22164)Success in time 0.182 s
%------------------------------------------------------------------------------
