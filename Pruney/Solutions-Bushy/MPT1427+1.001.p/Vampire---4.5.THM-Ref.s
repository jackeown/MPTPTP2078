%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1427+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:54 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  327 ( 786 expanded)
%              Number of leaves         :   74 ( 372 expanded)
%              Depth                    :   11
%              Number of atoms          : 1362 (3131 expanded)
%              Number of equality atoms :  114 ( 414 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1935,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f109,f114,f119,f124,f129,f134,f139,f144,f149,f159,f169,f178,f188,f194,f206,f225,f235,f248,f292,f293,f300,f324,f329,f415,f439,f635,f639,f644,f650,f655,f666,f701,f790,f841,f851,f863,f1037,f1076,f1086,f1126,f1352,f1356,f1368,f1427,f1548,f1559,f1567,f1856,f1863,f1887,f1893,f1910,f1918,f1925,f1931,f1934])).

fof(f1934,plain,
    ( ~ spl8_67
    | ~ spl8_68
    | ~ spl8_102
    | ~ spl8_117
    | spl8_144 ),
    inference(avatar_contradiction_clause,[],[f1932])).

fof(f1932,plain,
    ( $false
    | ~ spl8_67
    | ~ spl8_68
    | ~ spl8_102
    | ~ spl8_117
    | spl8_144 ),
    inference(unit_resulting_resolution,[],[f649,f654,f1930,f1580])).

fof(f1580,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_tarski(X0,X1),k1_relat_1(k3_funct_4(sK6,sK7)))
        | ~ m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_102
    | ~ spl8_117 ),
    inference(backward_demodulation,[],[f1367,f1566])).

fof(f1566,plain,
    ( k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) = k1_relat_1(k3_funct_4(sK6,sK7))
    | ~ spl8_117 ),
    inference(avatar_component_clause,[],[f1564])).

fof(f1564,plain,
    ( spl8_117
  <=> k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) = k1_relat_1(k3_funct_4(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_117])])).

fof(f1367,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_tarski(X0,X1),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | ~ m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f1366])).

fof(f1366,plain,
    ( spl8_102
  <=> ! [X1,X0] :
        ( m1_subset_1(k4_tarski(X0,X1),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | ~ m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f1930,plain,
    ( ~ m1_subset_1(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | spl8_144 ),
    inference(avatar_component_clause,[],[f1928])).

fof(f1928,plain,
    ( spl8_144
  <=> m1_subset_1(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_144])])).

fof(f654,plain,
    ( m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl8_68
  <=> m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f649,plain,
    ( m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f647])).

fof(f647,plain,
    ( spl8_67
  <=> m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f1931,plain,
    ( ~ spl8_144
    | spl8_105
    | spl8_143 ),
    inference(avatar_split_clause,[],[f1926,f1922,f1424,f1928])).

fof(f1424,plain,
    ( spl8_105
  <=> v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_105])])).

fof(f1922,plain,
    ( spl8_143
  <=> r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_143])])).

fof(f1926,plain,
    ( v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | spl8_143 ),
    inference(resolution,[],[f1924,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f1924,plain,
    ( ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | spl8_143 ),
    inference(avatar_component_clause,[],[f1922])).

fof(f1925,plain,
    ( ~ spl8_14
    | ~ spl8_143
    | ~ spl8_1
    | ~ spl8_13
    | ~ spl8_2
    | spl8_142 ),
    inference(avatar_split_clause,[],[f1920,f1915,f96,f156,f91,f1922,f166])).

fof(f166,plain,
    ( spl8_14
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f91,plain,
    ( spl8_1
  <=> v1_funct_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f156,plain,
    ( spl8_13
  <=> v1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f96,plain,
    ( spl8_2
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f1915,plain,
    ( spl8_142
  <=> k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) = k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_142])])).

fof(f1920,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_relat_1(sK6)
    | spl8_142 ),
    inference(trivial_inequality_removal,[],[f1919])).

fof(f1919,plain,
    ( k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK7)
    | ~ v1_funct_1(sK7)
    | ~ r2_hidden(k4_tarski(k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)),k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_relat_1(sK6)
    | spl8_142 ),
    inference(superposition,[],[f1917,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3)) = k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3))
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X5)
      | ~ v1_funct_1(X5)
      | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3)) = k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3))
          | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
          | ~ v1_funct_1(X5)
          | ~ v1_relat_1(X5) )
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ! [X5] :
          ( k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3)) = k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3))
          | ~ r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
          | ~ v1_funct_1(X5)
          | ~ v1_relat_1(X5) )
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_relat_1(X4) )
     => ! [X5] :
          ( ( v1_funct_1(X5)
            & v1_relat_1(X5) )
         => ( r2_hidden(k4_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)),k1_relat_1(k3_funct_4(X4,X5)))
           => k1_binop_1(k3_funct_4(X4,X5),k4_tarski(X0,X1),k4_tarski(X2,X3)) = k4_tarski(k1_binop_1(X4,X0,X2),k1_binop_1(X5,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_4)).

fof(f1917,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5))
    | spl8_142 ),
    inference(avatar_component_clause,[],[f1915])).

fof(f1918,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_142
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_18
    | spl8_141 ),
    inference(avatar_split_clause,[],[f1913,f1907,f203,f232,f222,f1915,f116,f111,f91])).

fof(f111,plain,
    ( spl8_5
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f116,plain,
    ( spl8_6
  <=> m1_subset_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f222,plain,
    ( spl8_19
  <=> v1_funct_2(sK7,k1_relat_1(sK7),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f232,plain,
    ( spl8_21
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f203,plain,
    ( spl8_18
  <=> k2_zfmisc_1(sK1,sK1) = k1_relat_1(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f1907,plain,
    ( spl8_141
  <=> k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) = k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_141])])).

fof(f1913,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5))
    | ~ m1_subset_1(sK4,sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(sK7)
    | ~ spl8_18
    | spl8_141 ),
    inference(forward_demodulation,[],[f1912,f205])).

fof(f205,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relat_1(sK7)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1912,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(sK7)
    | ~ spl8_18
    | spl8_141 ),
    inference(forward_demodulation,[],[f1911,f205])).

fof(f1911,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k1_binop_1(sK7,sK4,sK5))
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ m1_subset_1(sK4,sK1)
    | ~ m1_subset_1(sK5,sK1)
    | ~ v1_funct_1(sK7)
    | spl8_141 ),
    inference(superposition,[],[f1909,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => k4_binop_1(X0,X1,X2,X3) = k1_binop_1(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_binop_1)).

fof(f1909,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | spl8_141 ),
    inference(avatar_component_clause,[],[f1907])).

fof(f1910,plain,
    ( ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_141
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_30
    | spl8_139 ),
    inference(avatar_split_clause,[],[f1897,f1890,f297,f326,f321,f1907,f126,f121,f96])).

fof(f121,plain,
    ( spl8_7
  <=> m1_subset_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f126,plain,
    ( spl8_8
  <=> m1_subset_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f321,plain,
    ( spl8_32
  <=> v1_funct_2(sK6,k1_relat_1(sK6),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f326,plain,
    ( spl8_33
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f297,plain,
    ( spl8_30
  <=> k2_zfmisc_1(sK0,sK0) = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f1890,plain,
    ( spl8_139
  <=> k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) = k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_139])])).

fof(f1897,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_139 ),
    inference(forward_demodulation,[],[f1896,f299])).

fof(f299,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relat_1(sK6)
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f297])).

fof(f1896,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_139 ),
    inference(forward_demodulation,[],[f1894,f299])).

fof(f1894,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k1_binop_1(sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK3,sK0)
    | ~ v1_funct_1(sK6)
    | spl8_139 ),
    inference(superposition,[],[f1892,f76])).

fof(f1892,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | spl8_139 ),
    inference(avatar_component_clause,[],[f1890])).

fof(f1893,plain,
    ( spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_3
    | ~ spl8_139
    | spl8_138 ),
    inference(avatar_split_clause,[],[f1888,f1884,f1890,f101,f121,f111,f106])).

fof(f106,plain,
    ( spl8_4
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f101,plain,
    ( spl8_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f1884,plain,
    ( spl8_138
  <=> k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) = k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_138])])).

fof(f1888,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k4_tarski(sK3,sK5)) != k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK0)
    | spl8_138 ),
    inference(superposition,[],[f1886,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3)
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => k1_domain_1(X0,X1,X2,X3) = k4_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_domain_1)).

fof(f1886,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) != k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | spl8_138 ),
    inference(avatar_component_clause,[],[f1884])).

fof(f1887,plain,
    ( spl8_4
    | ~ spl8_81
    | ~ spl8_82
    | spl8_3
    | ~ spl8_138
    | spl8_136 ),
    inference(avatar_split_clause,[],[f1866,f1860,f1884,f101,f827,f823,f106])).

fof(f823,plain,
    ( spl8_81
  <=> m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_81])])).

fof(f827,plain,
    ( spl8_82
  <=> m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_82])])).

fof(f1860,plain,
    ( spl8_136
  <=> k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) = k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_136])])).

fof(f1866,plain,
    ( k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) != k4_tarski(k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0)
    | ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1)
    | v1_xboole_0(sK0)
    | spl8_136 ),
    inference(superposition,[],[f1862,f69])).

fof(f1862,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | spl8_136 ),
    inference(avatar_component_clause,[],[f1860])).

fof(f1863,plain,
    ( spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_3
    | ~ spl8_136
    | spl8_135 ),
    inference(avatar_split_clause,[],[f1857,f1853,f1860,f101,f126,f116,f106])).

fof(f1853,plain,
    ( spl8_135
  <=> k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) = k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_135])])).

fof(f1857,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k4_tarski(sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK4,sK1)
    | v1_xboole_0(sK0)
    | spl8_135 ),
    inference(superposition,[],[f1855,f69])).

fof(f1855,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | spl8_135 ),
    inference(avatar_component_clause,[],[f1853])).

fof(f1856,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_135
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_18
    | ~ spl8_30
    | spl8_66 ),
    inference(avatar_split_clause,[],[f713,f632,f297,f203,f232,f222,f326,f321,f1853,f91,f96])).

fof(f632,plain,
    ( spl8_66
  <=> k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) = k1_binop_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_66])])).

fof(f713,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_66 ),
    inference(forward_demodulation,[],[f712,f205])).

fof(f712,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_66 ),
    inference(forward_demodulation,[],[f711,f205])).

fof(f711,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_66 ),
    inference(forward_demodulation,[],[f710,f299])).

fof(f710,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_66 ),
    inference(forward_demodulation,[],[f707,f299])).

fof(f707,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k3_funct_4(sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | spl8_66 ),
    inference(superposition,[],[f634,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3)
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => k6_filter_1(X0,X1,X2,X3) = k3_funct_4(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_filter_1)).

fof(f634,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | spl8_66 ),
    inference(avatar_component_clause,[],[f632])).

fof(f1567,plain,
    ( ~ spl8_115
    | spl8_117
    | ~ spl8_116 ),
    inference(avatar_split_clause,[],[f1561,f1556,f1564,f1545])).

fof(f1545,plain,
    ( spl8_115
  <=> m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_115])])).

fof(f1556,plain,
    ( spl8_116
  <=> k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) = k1_relset_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_116])])).

fof(f1561,plain,
    ( k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) = k1_relat_1(k3_funct_4(sK6,sK7))
    | ~ m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_116 ),
    inference(superposition,[],[f1558,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f1558,plain,
    ( k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) = k1_relset_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))
    | ~ spl8_116 ),
    inference(avatar_component_clause,[],[f1556])).

fof(f1559,plain,
    ( ~ spl8_93
    | spl8_116
    | spl8_85
    | ~ spl8_115 ),
    inference(avatar_split_clause,[],[f1552,f1545,f860,f1556,f1083])).

fof(f1083,plain,
    ( spl8_93
  <=> v1_funct_2(k3_funct_4(sK6,sK7),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_93])])).

fof(f860,plain,
    ( spl8_85
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_85])])).

fof(f1552,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) = k1_relset_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1),k3_funct_4(sK6,sK7))
    | ~ v1_funct_2(k3_funct_4(sK6,sK7),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_115 ),
    inference(resolution,[],[f1547,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | o_0_0_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(definition_unfolding,[],[f68,f57])).

fof(f57,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f1547,plain,
    ( m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_115 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f1548,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_19
    | ~ spl8_21
    | spl8_115
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_64
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f1542,f1034,f624,f297,f203,f1545,f232,f222,f326,f321,f91,f96])).

fof(f624,plain,
    ( spl8_64
  <=> m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f1034,plain,
    ( spl8_91
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_91])])).

fof(f1542,plain,
    ( m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_64
    | ~ spl8_91 ),
    inference(forward_demodulation,[],[f690,f1036])).

fof(f1036,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7))
    | ~ spl8_91 ),
    inference(avatar_component_clause,[],[f1034])).

fof(f690,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_64 ),
    inference(forward_demodulation,[],[f689,f205])).

fof(f689,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_64 ),
    inference(forward_demodulation,[],[f688,f205])).

fof(f688,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | ~ spl8_64 ),
    inference(forward_demodulation,[],[f687,f299])).

fof(f687,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | ~ spl8_64 ),
    inference(forward_demodulation,[],[f686,f299])).

fof(f686,plain,
    ( m1_subset_1(k3_funct_4(sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_64 ),
    inference(superposition,[],[f625,f71])).

fof(f625,plain,
    ( m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_64 ),
    inference(avatar_component_clause,[],[f624])).

fof(f1427,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_105
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_18
    | ~ spl8_30
    | spl8_92 ),
    inference(avatar_split_clause,[],[f1081,f1073,f297,f203,f232,f222,f326,f321,f1424,f91,f96])).

fof(f1073,plain,
    ( spl8_92
  <=> v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_92])])).

fof(f1081,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_92 ),
    inference(forward_demodulation,[],[f1080,f205])).

fof(f1080,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_92 ),
    inference(forward_demodulation,[],[f1079,f205])).

fof(f1079,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_92 ),
    inference(forward_demodulation,[],[f1078,f299])).

fof(f1078,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_92 ),
    inference(forward_demodulation,[],[f1077,f299])).

fof(f1077,plain,
    ( ~ v1_xboole_0(k1_relat_1(k3_funct_4(sK6,sK7)))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | spl8_92 ),
    inference(superposition,[],[f1075,f71])).

fof(f1075,plain,
    ( ~ v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
    | spl8_92 ),
    inference(avatar_component_clause,[],[f1073])).

fof(f1368,plain,
    ( spl8_90
    | spl8_102
    | ~ spl8_101 ),
    inference(avatar_split_clause,[],[f1360,f1350,f1366,f964])).

fof(f964,plain,
    ( spl8_90
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_90])])).

fof(f1350,plain,
    ( spl8_101
  <=> ! [X5,X6] :
        ( m1_subset_1(k1_domain_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),X5,X6),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X5,k2_zfmisc_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_101])])).

fof(f1360,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_tarski(X0,X1),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_101 ),
    inference(duplicate_literal_removal,[],[f1358])).

fof(f1358,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k4_tarski(X0,X1),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X0,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X1,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_101 ),
    inference(superposition,[],[f1351,f69])).

fof(f1351,plain,
    ( ! [X6,X5] :
        ( m1_subset_1(k1_domain_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),X5,X6),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X5,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_101 ),
    inference(avatar_component_clause,[],[f1350])).

fof(f1356,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_90 ),
    inference(avatar_contradiction_clause,[],[f1353])).

fof(f1353,plain,
    ( $false
    | spl8_3
    | spl8_4
    | ~ spl8_90 ),
    inference(unit_resulting_resolution,[],[f108,f103,f965,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_subset_1)).

fof(f965,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_90 ),
    inference(avatar_component_clause,[],[f964])).

fof(f103,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f108,plain,
    ( ~ v1_xboole_0(sK0)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1352,plain,
    ( spl8_90
    | spl8_101
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f1265,f1034,f1350,f964])).

fof(f1265,plain,
    ( ! [X6,X5] :
        ( m1_subset_1(k1_domain_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),X5,X6),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X5,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_91 ),
    inference(duplicate_literal_removal,[],[f1253])).

fof(f1253,plain,
    ( ! [X6,X5] :
        ( m1_subset_1(k1_domain_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1),X5,X6),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X5,k2_zfmisc_1(sK0,sK1))
        | ~ m1_subset_1(X6,k2_zfmisc_1(sK0,sK1))
        | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_91 ),
    inference(superposition,[],[f70,f1036])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | ~ m1_subset_1(X3,X1)
      | ~ m1_subset_1(X2,X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X1)
        & m1_subset_1(X2,X0)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k1_domain_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_domain_1)).

fof(f1126,plain,
    ( spl8_4
    | spl8_3
    | ~ spl8_17
    | ~ spl8_85 ),
    inference(avatar_split_clause,[],[f1109,f860,f185,f101,f106])).

fof(f185,plain,
    ( spl8_17
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f1109,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | ~ spl8_85 ),
    inference(superposition,[],[f60,f862])).

fof(f862,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | ~ spl8_85 ),
    inference(avatar_component_clause,[],[f860])).

fof(f1086,plain,
    ( spl8_93
    | ~ spl8_77
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f1040,f1034,f787,f1083])).

fof(f787,plain,
    ( spl8_77
  <=> v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f1040,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_77
    | ~ spl8_91 ),
    inference(backward_demodulation,[],[f789,f1036])).

fof(f789,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f787])).

fof(f1076,plain,
    ( spl8_90
    | ~ spl8_92
    | ~ spl8_91 ),
    inference(avatar_split_clause,[],[f1058,f1034,f1073,f964])).

fof(f1058,plain,
    ( ~ v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_91 ),
    inference(duplicate_literal_removal,[],[f1044])).

fof(f1044,plain,
    ( ~ v1_xboole_0(k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7)))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | ~ spl8_91 ),
    inference(superposition,[],[f60,f1036])).

fof(f1037,plain,
    ( ~ spl8_64
    | spl8_91
    | ~ spl8_84 ),
    inference(avatar_split_clause,[],[f1009,f856,f1034,f624])).

fof(f856,plain,
    ( spl8_84
  <=> k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f1009,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relat_1(k6_filter_1(sK0,sK1,sK6,sK7))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ spl8_84 ),
    inference(superposition,[],[f858,f62])).

fof(f858,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f856])).

fof(f863,plain,
    ( ~ spl8_65
    | spl8_84
    | spl8_85
    | ~ spl8_64 ),
    inference(avatar_split_clause,[],[f684,f624,f860,f856,f628])).

fof(f628,plain,
    ( spl8_65
  <=> v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_65])])).

fof(f684,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k1_relset_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_64 ),
    inference(resolution,[],[f625,f79])).

fof(f851,plain,
    ( ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_33
    | spl8_82 ),
    inference(avatar_contradiction_clause,[],[f846])).

fof(f846,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_7
    | ~ spl8_8
    | ~ spl8_30
    | ~ spl8_32
    | ~ spl8_33
    | spl8_82 ),
    inference(unit_resulting_resolution,[],[f98,f123,f128,f323,f328,f829,f311])).

fof(f311,plain,
    ( ! [X10,X11,X9] :
        ( m1_subset_1(k4_binop_1(sK0,X9,X10,X11),sK0)
        | ~ v1_funct_2(X9,k1_relat_1(sK6),sK0)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X10,sK0)
        | ~ m1_subset_1(X11,sK0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0))) )
    | ~ spl8_30 ),
    inference(superposition,[],[f75,f299])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X3,X0)
      | m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => m1_subset_1(k4_binop_1(X0,X1,X2,X3),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_binop_1)).

fof(f829,plain,
    ( ~ m1_subset_1(k4_binop_1(sK0,sK6,sK2,sK3),sK0)
    | spl8_82 ),
    inference(avatar_component_clause,[],[f827])).

fof(f328,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f326])).

fof(f323,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f321])).

fof(f128,plain,
    ( m1_subset_1(sK2,sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f123,plain,
    ( m1_subset_1(sK3,sK0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f98,plain,
    ( v1_funct_1(sK6)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f841,plain,
    ( ~ spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | spl8_81 ),
    inference(avatar_contradiction_clause,[],[f836])).

fof(f836,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_5
    | ~ spl8_6
    | ~ spl8_18
    | ~ spl8_19
    | ~ spl8_21
    | spl8_81 ),
    inference(unit_resulting_resolution,[],[f93,f113,f118,f224,f234,f825,f217])).

fof(f217,plain,
    ( ! [X10,X11,X9] :
        ( m1_subset_1(k4_binop_1(sK1,X9,X10,X11),sK1)
        | ~ v1_funct_2(X9,k1_relat_1(sK7),sK1)
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X10,sK1)
        | ~ m1_subset_1(X11,sK1)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1))) )
    | ~ spl8_18 ),
    inference(superposition,[],[f75,f205])).

fof(f825,plain,
    ( ~ m1_subset_1(k4_binop_1(sK1,sK7,sK4,sK5),sK1)
    | spl8_81 ),
    inference(avatar_component_clause,[],[f823])).

fof(f234,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f232])).

fof(f224,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f118,plain,
    ( m1_subset_1(sK4,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f113,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f93,plain,
    ( v1_funct_1(sK7)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f790,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | spl8_77
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_65 ),
    inference(avatar_split_clause,[],[f706,f628,f297,f203,f232,f222,f326,f321,f787,f91,f96])).

fof(f706,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_65 ),
    inference(forward_demodulation,[],[f705,f205])).

fof(f705,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | ~ spl8_65 ),
    inference(forward_demodulation,[],[f704,f205])).

fof(f704,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | ~ spl8_65 ),
    inference(forward_demodulation,[],[f703,f299])).

fof(f703,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | ~ spl8_65 ),
    inference(forward_demodulation,[],[f702,f299])).

fof(f702,plain,
    ( v1_funct_2(k3_funct_4(sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_65 ),
    inference(superposition,[],[f629,f71])).

fof(f629,plain,
    ( v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_65 ),
    inference(avatar_component_clause,[],[f628])).

fof(f701,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_18
    | ~ spl8_30
    | spl8_65 ),
    inference(avatar_split_clause,[],[f672,f628,f297,f203,f232,f222,f326,f321,f91,f96])).

fof(f672,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_65 ),
    inference(forward_demodulation,[],[f671,f205])).

fof(f671,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_65 ),
    inference(forward_demodulation,[],[f670,f205])).

fof(f670,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_65 ),
    inference(forward_demodulation,[],[f669,f299])).

fof(f669,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_65 ),
    inference(forward_demodulation,[],[f667,f299])).

fof(f667,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | spl8_65 ),
    inference(resolution,[],[f630,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
        & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
        & v1_funct_2(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))
        & v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_filter_1)).

fof(f630,plain,
    ( ~ v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | spl8_65 ),
    inference(avatar_component_clause,[],[f628])).

fof(f666,plain,
    ( ~ spl8_2
    | ~ spl8_1
    | ~ spl8_32
    | ~ spl8_33
    | ~ spl8_19
    | ~ spl8_21
    | ~ spl8_18
    | ~ spl8_30
    | spl8_64 ),
    inference(avatar_split_clause,[],[f661,f624,f297,f203,f232,f222,f326,f321,f91,f96])).

fof(f661,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_64 ),
    inference(forward_demodulation,[],[f660,f205])).

fof(f660,plain,
    ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_18
    | ~ spl8_30
    | spl8_64 ),
    inference(forward_demodulation,[],[f659,f205])).

fof(f659,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_64 ),
    inference(forward_demodulation,[],[f658,f299])).

fof(f658,plain,
    ( ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | ~ spl8_30
    | spl8_64 ),
    inference(forward_demodulation,[],[f656,f299])).

fof(f656,plain,
    ( ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ v1_funct_1(sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ v1_funct_1(sK6)
    | spl8_64 ),
    inference(resolution,[],[f626,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k6_filter_1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X1)),k2_zfmisc_1(X0,X1))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f626,plain,
    ( ~ m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | spl8_64 ),
    inference(avatar_component_clause,[],[f624])).

fof(f655,plain,
    ( spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_3
    | spl8_68
    | ~ spl8_63 ),
    inference(avatar_split_clause,[],[f645,f620,f652,f101,f126,f116,f106])).

fof(f620,plain,
    ( spl8_63
  <=> m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f645,plain,
    ( m1_subset_1(k4_tarski(sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK2,sK0)
    | ~ m1_subset_1(sK4,sK1)
    | v1_xboole_0(sK0)
    | ~ spl8_63 ),
    inference(superposition,[],[f621,f69])).

fof(f621,plain,
    ( m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f620])).

fof(f650,plain,
    ( spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_3
    | spl8_67
    | ~ spl8_62 ),
    inference(avatar_split_clause,[],[f640,f616,f647,f101,f121,f111,f106])).

fof(f616,plain,
    ( spl8_62
  <=> m1_subset_1(k1_domain_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_62])])).

fof(f640,plain,
    ( m1_subset_1(k4_tarski(sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,sK0)
    | ~ m1_subset_1(sK5,sK1)
    | v1_xboole_0(sK0)
    | ~ spl8_62 ),
    inference(superposition,[],[f617,f69])).

fof(f617,plain,
    ( m1_subset_1(k1_domain_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_62 ),
    inference(avatar_component_clause,[],[f616])).

fof(f644,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_63 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | spl8_3
    | spl8_4
    | ~ spl8_6
    | ~ spl8_8
    | spl8_63 ),
    inference(unit_resulting_resolution,[],[f108,f103,f118,f128,f622,f70])).

fof(f622,plain,
    ( ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | spl8_63 ),
    inference(avatar_component_clause,[],[f620])).

fof(f639,plain,
    ( spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_62 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | spl8_3
    | spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | spl8_62 ),
    inference(unit_resulting_resolution,[],[f108,f103,f113,f123,f618,f70])).

fof(f618,plain,
    ( ~ m1_subset_1(k1_domain_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | spl8_62 ),
    inference(avatar_component_clause,[],[f616])).

fof(f635,plain,
    ( ~ spl8_46
    | ~ spl8_62
    | ~ spl8_63
    | ~ spl8_64
    | ~ spl8_65
    | ~ spl8_66
    | spl8_23 ),
    inference(avatar_split_clause,[],[f262,f245,f632,f628,f624,f620,f616,f436])).

fof(f436,plain,
    ( spl8_46
  <=> v1_funct_1(k6_filter_1(sK0,sK1,sK6,sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f245,plain,
    ( spl8_23
  <=> k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) = k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f262,plain,
    ( k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) != k1_binop_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5))
    | ~ v1_funct_2(k6_filter_1(sK0,sK1,sK6,sK7),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k6_filter_1(sK0,sK1,sK6,sK7),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK2,sK4),k2_zfmisc_1(sK0,sK1))
    | ~ m1_subset_1(k1_domain_1(sK0,sK1,sK3,sK5),k2_zfmisc_1(sK0,sK1))
    | ~ v1_funct_1(k6_filter_1(sK0,sK1,sK6,sK7))
    | spl8_23 ),
    inference(superposition,[],[f247,f76])).

fof(f247,plain,
    ( k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) != k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5))
    | spl8_23 ),
    inference(avatar_component_clause,[],[f245])).

fof(f439,plain,
    ( ~ spl8_32
    | ~ spl8_2
    | spl8_46
    | ~ spl8_30
    | ~ spl8_33
    | ~ spl8_43 ),
    inference(avatar_split_clause,[],[f434,f413,f326,f297,f436,f96,f321])).

fof(f413,plain,
    ( spl8_43
  <=> ! [X3,X2] :
        ( ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
        | v1_funct_1(k6_filter_1(X3,sK1,X2,sK7))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_43])])).

fof(f434,plain,
    ( v1_funct_1(k6_filter_1(sK0,sK1,sK6,sK7))
    | ~ v1_funct_1(sK6)
    | ~ v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl8_30
    | ~ spl8_33
    | ~ spl8_43 ),
    inference(resolution,[],[f418,f328])).

fof(f418,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
        | v1_funct_1(k6_filter_1(sK0,sK1,X1,sK7))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_relat_1(sK6),sK0) )
    | ~ spl8_30
    | ~ spl8_43 ),
    inference(superposition,[],[f414,f299])).

fof(f414,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | v1_funct_1(k6_filter_1(X3,sK1,X2,sK7))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3) )
    | ~ spl8_43 ),
    inference(avatar_component_clause,[],[f413])).

fof(f415,plain,
    ( ~ spl8_1
    | spl8_43
    | ~ spl8_19
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f395,f203,f141,f222,f413,f91])).

fof(f141,plain,
    ( spl8_11
  <=> m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f395,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(sK7,k1_relat_1(sK7),sK1)
        | ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_1(sK7)
        | ~ v1_funct_1(X2)
        | v1_funct_1(k6_filter_1(X3,sK1,X2,sK7)) )
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f151,f205])).

fof(f151,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X2,k2_zfmisc_1(X3,X3),X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X3,X3),X3)))
        | ~ v1_funct_1(sK7)
        | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
        | ~ v1_funct_1(X2)
        | v1_funct_1(k6_filter_1(X3,sK1,X2,sK7)) )
    | ~ spl8_11 ),
    inference(resolution,[],[f143,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X2)
      | v1_funct_1(k6_filter_1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f143,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f141])).

fof(f329,plain,
    ( spl8_33
    | ~ spl8_12
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f302,f297,f146,f326])).

fof(f146,plain,
    ( spl8_12
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f302,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK6),sK0)))
    | ~ spl8_12
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f148,f299])).

fof(f148,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f146])).

fof(f324,plain,
    ( spl8_32
    | ~ spl8_10
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f303,f297,f136,f321])).

fof(f136,plain,
    ( spl8_10
  <=> v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f303,plain,
    ( v1_funct_2(sK6,k1_relat_1(sK6),sK0)
    | ~ spl8_10
    | ~ spl8_30 ),
    inference(backward_demodulation,[],[f138,f299])).

fof(f138,plain,
    ( v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f136])).

fof(f300,plain,
    ( ~ spl8_12
    | spl8_30
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f294,f285,f297,f146])).

fof(f285,plain,
    ( spl8_28
  <=> k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f294,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relat_1(sK6)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0)))
    | ~ spl8_28 ),
    inference(superposition,[],[f287,f62])).

fof(f287,plain,
    ( k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6)
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f285])).

fof(f293,plain,
    ( o_0_0_xboole_0 != sK0
    | v1_xboole_0(sK0)
    | ~ v1_xboole_0(o_0_0_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f292,plain,
    ( ~ spl8_10
    | spl8_28
    | spl8_29
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f163,f146,f289,f285,f136])).

fof(f289,plain,
    ( spl8_29
  <=> o_0_0_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f163,plain,
    ( o_0_0_xboole_0 = sK0
    | k2_zfmisc_1(sK0,sK0) = k1_relset_1(k2_zfmisc_1(sK0,sK0),sK0,sK6)
    | ~ v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0)
    | ~ spl8_12 ),
    inference(resolution,[],[f148,f79])).

fof(f248,plain,(
    ~ spl8_23 ),
    inference(avatar_split_clause,[],[f46,f245])).

fof(f46,plain,(
    k4_binop_1(k2_zfmisc_1(sK0,sK1),k6_filter_1(sK0,sK1,sK6,sK7),k1_domain_1(sK0,sK1,sK2,sK4),k1_domain_1(sK0,sK1,sK3,sK5)) != k1_domain_1(sK0,sK1,k4_binop_1(sK0,sK6,sK2,sK3),k4_binop_1(sK1,sK7,sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5)) != k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                  & v1_funct_1(X7) )
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                              & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,X1) )
                      & m1_subset_1(X4,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ? [X7] :
                                  ( k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5)) != k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5))
                                  & m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                  & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                  & v1_funct_1(X7) )
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                              & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                              & v1_funct_1(X6) )
                          & m1_subset_1(X5,X1) )
                      & m1_subset_1(X4,X1) )
                  & m1_subset_1(X3,X0) )
              & m1_subset_1(X2,X0) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,X0)
                   => ! [X4] :
                        ( m1_subset_1(X4,X1)
                       => ! [X5] :
                            ( m1_subset_1(X5,X1)
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                                  & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                                  & v1_funct_1(X6) )
                               => ! [X7] :
                                    ( ( m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                      & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                      & v1_funct_1(X7) )
                                   => k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5)) = k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => ! [X5] :
                          ( m1_subset_1(X5,X1)
                         => ! [X6] :
                              ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                                & v1_funct_2(X6,k2_zfmisc_1(X0,X0),X0)
                                & v1_funct_1(X6) )
                             => ! [X7] :
                                  ( ( m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                                    & v1_funct_2(X7,k2_zfmisc_1(X1,X1),X1)
                                    & v1_funct_1(X7) )
                                 => k4_binop_1(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X6,X7),k1_domain_1(X0,X1,X2,X4),k1_domain_1(X0,X1,X3,X5)) = k1_domain_1(X0,X1,k4_binop_1(X0,X6,X2,X3),k4_binop_1(X1,X7,X4,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_filter_1)).

fof(f235,plain,
    ( spl8_21
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f208,f203,f141,f232])).

fof(f208,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK7),sK1)))
    | ~ spl8_11
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f143,f205])).

fof(f225,plain,
    ( spl8_19
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f209,f203,f131,f222])).

fof(f131,plain,
    ( spl8_9
  <=> v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f209,plain,
    ( v1_funct_2(sK7,k1_relat_1(sK7),sK1)
    | ~ spl8_9
    | ~ spl8_18 ),
    inference(backward_demodulation,[],[f133,f205])).

fof(f133,plain,
    ( v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f131])).

fof(f206,plain,
    ( ~ spl8_11
    | spl8_18
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f200,f171,f203,f141])).

fof(f171,plain,
    ( spl8_15
  <=> k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f200,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relat_1(sK7)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1)))
    | ~ spl8_15 ),
    inference(superposition,[],[f173,f62])).

fof(f173,plain,
    ( k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7)
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f171])).

fof(f194,plain,(
    spl8_17 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl8_17 ),
    inference(unit_resulting_resolution,[],[f56,f187])).

fof(f187,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl8_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f56,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f188,plain,
    ( ~ spl8_17
    | spl8_3
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f183,f175,f101,f185])).

fof(f175,plain,
    ( spl8_16
  <=> o_0_0_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f183,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl8_3
    | ~ spl8_16 ),
    inference(backward_demodulation,[],[f103,f177])).

fof(f177,plain,
    ( o_0_0_xboole_0 = sK1
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f178,plain,
    ( ~ spl8_9
    | spl8_15
    | spl8_16
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f153,f141,f175,f171,f131])).

fof(f153,plain,
    ( o_0_0_xboole_0 = sK1
    | k2_zfmisc_1(sK1,sK1) = k1_relset_1(k2_zfmisc_1(sK1,sK1),sK1,sK7)
    | ~ v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1)
    | ~ spl8_11 ),
    inference(resolution,[],[f143,f79])).

fof(f169,plain,
    ( spl8_14
    | ~ spl8_12 ),
    inference(avatar_split_clause,[],[f164,f146,f166])).

fof(f164,plain,
    ( v1_relat_1(sK6)
    | ~ spl8_12 ),
    inference(resolution,[],[f148,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,
    ( spl8_13
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f154,f141,f156])).

fof(f154,plain,
    ( v1_relat_1(sK7)
    | ~ spl8_11 ),
    inference(resolution,[],[f143,f61])).

fof(f149,plain,(
    spl8_12 ),
    inference(avatar_split_clause,[],[f49,f146])).

fof(f49,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK0,sK0),sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f144,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f45,f141])).

fof(f45,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(sK1,sK1),sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f139,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f48,f136])).

fof(f48,plain,(
    v1_funct_2(sK6,k2_zfmisc_1(sK0,sK0),sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f134,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f44,f131])).

fof(f44,plain,(
    v1_funct_2(sK7,k2_zfmisc_1(sK1,sK1),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f129,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f53,f126])).

fof(f53,plain,(
    m1_subset_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f124,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f52,f121])).

fof(f52,plain,(
    m1_subset_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f119,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f51,f116])).

fof(f51,plain,(
    m1_subset_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f114,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f50,f111])).

fof(f50,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f109,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f55,f106])).

fof(f55,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f43,f91])).

fof(f43,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f19])).

%------------------------------------------------------------------------------
