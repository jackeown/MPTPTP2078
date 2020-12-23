%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0699+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:29 EST 2020

% Result     : Theorem 6.53s
% Output     : Refutation 6.72s
% Verified   : 
% Statistics : Number of formulae       : 1155 (12152 expanded)
%              Number of leaves         :  170 (4516 expanded)
%              Depth                    :   27
%              Number of atoms          : 5323 (79177 expanded)
%              Number of equality atoms :  377 (19643 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :   19 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8351,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f124,f129,f136,f141,f147,f152,f160,f165,f170,f178,f183,f188,f196,f201,f206,f214,f219,f224,f237,f243,f248,f256,f262,f267,f275,f281,f286,f300,f308,f314,f319,f340,f346,f354,f365,f371,f376,f399,f406,f412,f420,f426,f440,f447,f453,f470,f475,f480,f492,f502,f515,f520,f533,f546,f554,f563,f568,f581,f591,f666,f671,f676,f695,f805,f810,f815,f827,f863,f922,f927,f932,f944,f970,f1010,f1020,f1022,f1038,f1114,f1116,f1212,f1233,f1332,f1380,f1405,f1426,f1496,f1520,f1589,f1654,f1687,f1752,f1776,f1826,f1913,f2004,f2041,f2145,f2198,f2238,f2275,f2320,f2467,f2984,f3013,f3162,f3271,f3276,f3281,f3306,f4007,f4099,f4123,f4366,f4539,f4544,f4549,f4567,f5623,f5966,f5997,f5998,f5999,f6001,f6003,f6336,f6341,f6361,f6381,f6394,f6417,f6478,f6587,f6714,f6716,f6722,f7031,f7033,f7036,f7038,f7040,f7042,f7044,f7046,f7048,f7050,f7052,f7054,f7056,f7058,f7060,f7062,f7064,f7066,f7068,f7070,f7072,f7074,f7076,f7078,f7080,f7082,f7084,f7086,f7088,f7097,f7108,f7121,f7126,f7128,f7131,f7135,f7137,f7139,f7141,f7143,f7147,f7149,f7152,f7154,f7156,f7158,f7161,f7177,f7213,f7215,f7254,f7257,f7288,f7300,f7304,f7313,f7501,f7503,f7505,f7508,f7513,f7607,f7612,f7699,f7735,f7738,f7749,f7760,f7815,f7876,f7906,f7914,f7925,f7977,f8060,f8108,f8230,f8269,f8277,f8315,f8339,f8344])).

fof(f8344,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_133
    | ~ spl16_136
    | spl16_149 ),
    inference(avatar_contradiction_clause,[],[f8343])).

fof(f8343,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_133
    | ~ spl16_136
    | spl16_149 ),
    inference(subsumption_resolution,[],[f8342,f8267])).

fof(f8267,plain,
    ( ~ r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | spl16_149 ),
    inference(avatar_component_clause,[],[f8266])).

fof(f8266,plain,
    ( spl16_149
  <=> r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_149])])).

fof(f8342,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(forward_demodulation,[],[f8341,f7569])).

fof(f7569,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))) = sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_136 ),
    inference(forward_demodulation,[],[f7543,f7551])).

fof(f7551,plain,
    ( sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(sK6,sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_136 ),
    inference(unit_resulting_resolution,[],[f118,f123,f6586,f108])).

fof(f108,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK11(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK11(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK9(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK9(X0,X1),X1) )
              & ( ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
                  & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK9(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK11(X0,X5)) = X5
                    & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f39,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK9(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK9(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = sK9(X0,X1)
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
        & r2_hidden(sK10(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK11(X0,X5)) = X5
        & r2_hidden(sK11(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

fof(f6586,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | ~ spl16_136 ),
    inference(avatar_component_clause,[],[f6584])).

fof(f6584,plain,
    ( spl16_136
  <=> r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_136])])).

fof(f123,plain,
    ( v1_funct_1(sK6)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl16_2
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f118,plain,
    ( v1_relat_1(sK6)
    | ~ spl16_1 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl16_1
  <=> v1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f7543,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))))) = sK11(sK6,k1_funct_1(sK6,sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_136 ),
    inference(unit_resulting_resolution,[],[f6586,f798])).

fof(f798,plain,
    ( ! [X6] :
        ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,X6))) = sK11(sK6,k1_funct_1(sK6,sK11(sK6,X6)))
        | ~ r2_hidden(X6,k2_relat_1(sK6)) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f797,f118])).

fof(f797,plain,
    ( ! [X6] :
        ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,X6))) = sK11(sK6,k1_funct_1(sK6,sK11(sK6,X6)))
        | ~ r2_hidden(X6,k2_relat_1(sK6))
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f791,f123])).

fof(f791,plain,
    ( ! [X6] :
        ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,X6))) = sK11(sK6,k1_funct_1(sK6,sK11(sK6,X6)))
        | ~ r2_hidden(X6,k2_relat_1(sK6))
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(resolution,[],[f726,f109])).

fof(f109,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK11(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f726,plain,
    ( ! [X10] :
        ( ~ r2_hidden(X10,k1_relat_1(sK6))
        | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X10)) = sK11(sK6,k1_funct_1(sK6,X10)) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f725,f118])).

fof(f725,plain,
    ( ! [X10] :
        ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X10)) = sK11(sK6,k1_funct_1(sK6,X10))
        | ~ r2_hidden(X10,k1_relat_1(sK6))
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f718,f123])).

fof(f718,plain,
    ( ! [X10] :
        ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X10)) = sK11(sK6,k1_funct_1(sK6,X10))
        | ~ r2_hidden(X10,k1_relat_1(sK6))
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(resolution,[],[f710,f107])).

fof(f107,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f710,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK6))
        | k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f709,f118])).

fof(f709,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK6))
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f708,f123])).

fof(f708,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK6))
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(duplicate_literal_removal,[],[f701])).

fof(f701,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0)
        | ~ r2_hidden(X0,k2_relat_1(sK6))
        | ~ r2_hidden(X0,k2_relat_1(sK6))
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(superposition,[],[f463,f108])).

fof(f463,plain,
    ( ! [X3] :
        ( sK11(sK6,X3) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,X3)))
        | ~ r2_hidden(X3,k2_relat_1(sK6)) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f462,f118])).

fof(f462,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK6))
        | ~ v1_relat_1(sK6)
        | sK11(sK6,X3) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,X3))) )
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f460,f123])).

fof(f460,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK6))
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6)
        | sK11(sK6,X3) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,X3))) )
    | ~ spl16_35 ),
    inference(resolution,[],[f109,f428])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK6))
        | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 )
    | ~ spl16_35 ),
    inference(resolution,[],[f101,f353])).

fof(f353,plain,
    ( sP1(k2_funct_1(sK6),sK6)
    | ~ spl16_35 ),
    inference(avatar_component_clause,[],[f351])).

fof(f351,plain,
    ( spl16_35
  <=> sP1(k2_funct_1(sK6),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_35])])).

fof(f101,plain,(
    ! [X0,X5,X1] :
      ( ~ sP1(X0,X1)
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | k1_funct_1(X0,k1_funct_1(X1,X5)) = X5 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X0,X5,X1] :
      ( k1_funct_1(X0,X4) = X5
      | k1_funct_1(X1,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ( ( sK8(X0,X1) != k1_funct_1(X0,sK7(X0,X1))
            | ~ r2_hidden(sK7(X0,X1),k2_relat_1(X1)) )
          & sK7(X0,X1) = k1_funct_1(X1,sK8(X0,X1))
          & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(sK7(X0,X1),sK8(X0,X1),X1,X0)
        | k1_relat_1(X0) != k2_relat_1(X1) )
      & ( ( ! [X4,X5] :
              ( ( ( k1_funct_1(X0,X4) = X5
                  & r2_hidden(X4,k2_relat_1(X1)) )
                | k1_funct_1(X1,X5) != X4
                | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & sP0(X4,X5,X1,X0) )
          & k1_relat_1(X0) = k2_relat_1(X1) )
        | ~ sP1(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ( k1_funct_1(X0,X2) != X3
              | ~ r2_hidden(X2,k2_relat_1(X1)) )
            & k1_funct_1(X1,X3) = X2
            & r2_hidden(X3,k1_relat_1(X1)) )
          | ~ sP0(X2,X3,X1,X0) )
     => ( ( ( sK8(X0,X1) != k1_funct_1(X0,sK7(X0,X1))
            | ~ r2_hidden(sK7(X0,X1),k2_relat_1(X1)) )
          & sK7(X0,X1) = k1_funct_1(X1,sK8(X0,X1))
          & r2_hidden(sK8(X0,X1),k1_relat_1(X1)) )
        | ~ sP0(sK7(X0,X1),sK8(X0,X1),X1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ? [X2,X3] :
            ( ( ( k1_funct_1(X0,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(X1)) )
              & k1_funct_1(X1,X3) = X2
              & r2_hidden(X3,k1_relat_1(X1)) )
            | ~ sP0(X2,X3,X1,X0) )
        | k1_relat_1(X0) != k2_relat_1(X1) )
      & ( ( ! [X4,X5] :
              ( ( ( k1_funct_1(X0,X4) = X5
                  & r2_hidden(X4,k2_relat_1(X1)) )
                | k1_funct_1(X1,X5) != X4
                | ~ r2_hidden(X5,k1_relat_1(X1)) )
              & sP0(X4,X5,X1,X0) )
          & k1_relat_1(X0) = k2_relat_1(X1) )
        | ~ sP1(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2,X3] :
            ( ( ( k1_funct_1(X1,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(X0)) )
              & k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) )
            | ~ sP0(X2,X3,X0,X1) )
        | k2_relat_1(X0) != k1_relat_1(X1) )
      & ( ( ! [X2,X3] :
              ( ( ( k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) )
                | k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
              & sP0(X2,X3,X0,X1) )
          & k2_relat_1(X0) = k1_relat_1(X1) )
        | ~ sP1(X1,X0) ) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ( sP1(X1,X0)
        | ? [X2,X3] :
            ( ( ( k1_funct_1(X1,X2) != X3
                | ~ r2_hidden(X2,k2_relat_1(X0)) )
              & k1_funct_1(X0,X3) = X2
              & r2_hidden(X3,k1_relat_1(X0)) )
            | ~ sP0(X2,X3,X0,X1) )
        | k2_relat_1(X0) != k1_relat_1(X1) )
      & ( ( ! [X2,X3] :
              ( ( ( k1_funct_1(X1,X2) = X3
                  & r2_hidden(X2,k2_relat_1(X0)) )
                | k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
              & sP0(X2,X3,X0,X1) )
          & k2_relat_1(X0) = k1_relat_1(X1) )
        | ~ sP1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sP1(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( ( k1_funct_1(X1,X2) = X3
                & r2_hidden(X2,k2_relat_1(X0)) )
              | k1_funct_1(X0,X3) != X2
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
            & sP0(X2,X3,X0,X1) )
        & k2_relat_1(X0) = k1_relat_1(X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f8341,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_133 ),
    inference(subsumption_resolution,[],[f8340,f140])).

fof(f140,plain,
    ( v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl16_5
  <=> v1_relat_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f8340,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_7
    | ~ spl16_133 ),
    inference(subsumption_resolution,[],[f8331,f151])).

fof(f151,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl16_7
  <=> v1_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f8331,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_133 ),
    inference(resolution,[],[f6389,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK12(X0,X1,X2)),X1)
                | ~ r2_hidden(sK12(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK12(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK12(X0,X1,X2)),X1)
                  & r2_hidden(sK12(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK12(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK12(X0,X1,X2)),X1)
          | ~ r2_hidden(sK12(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK12(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK12(X0,X1,X2)),X1)
            & r2_hidden(sK12(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK12(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

fof(f6389,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ spl16_133 ),
    inference(avatar_component_clause,[],[f6387])).

fof(f6387,plain,
    ( spl16_133
  <=> r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_133])])).

fof(f8339,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_133
    | ~ spl16_136
    | spl16_149 ),
    inference(avatar_contradiction_clause,[],[f8338])).

fof(f8338,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_133
    | ~ spl16_136
    | spl16_149 ),
    inference(subsumption_resolution,[],[f8337,f8267])).

fof(f8337,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(forward_demodulation,[],[f8327,f7569])).

fof(f8327,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_133 ),
    inference(unit_resulting_resolution,[],[f140,f151,f6389,f111])).

fof(f8315,plain,
    ( ~ spl16_150
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_135 ),
    inference(avatar_split_clause,[],[f8253,f6414,f373,f351,f149,f138,f8312])).

fof(f8312,plain,
    ( spl16_150
  <=> r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_150])])).

fof(f373,plain,
    ( spl16_38
  <=> k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_38])])).

fof(f6414,plain,
    ( spl16_135
  <=> r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_135])])).

fof(f8253,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_135 ),
    inference(unit_resulting_resolution,[],[f6415,f606])).

fof(f606,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_relat_1(sK6))
        | ~ r2_hidden(X3,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f605,f465])).

fof(f465,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(k2_funct_1(sK6),X0),k2_relat_1(sK6))
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f464,f140])).

fof(f464,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(k2_funct_1(sK6),X0),k2_relat_1(sK6))
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f461,f151])).

fof(f461,plain,
    ( ! [X0] :
        ( r2_hidden(sK11(k2_funct_1(sK6),X0),k2_relat_1(sK6))
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_38 ),
    inference(superposition,[],[f109,f375])).

fof(f375,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | ~ spl16_38 ),
    inference(avatar_component_clause,[],[f373])).

fof(f605,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_relat_1(sK6))
        | ~ r2_hidden(sK11(k2_funct_1(sK6),X3),k2_relat_1(sK6))
        | ~ r2_hidden(X3,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f604,f140])).

fof(f604,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_relat_1(sK6))
        | ~ r2_hidden(sK11(k2_funct_1(sK6),X3),k2_relat_1(sK6))
        | ~ r2_hidden(X3,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_7
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f602,f151])).

fof(f602,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_relat_1(sK6))
        | ~ r2_hidden(sK11(k2_funct_1(sK6),X3),k2_relat_1(sK6))
        | ~ r2_hidden(X3,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_35 ),
    inference(superposition,[],[f593,f108])).

fof(f593,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),X3),k1_relat_1(sK6))
        | ~ r2_hidden(X3,k2_relat_1(sK6)) )
    | ~ spl16_35 ),
    inference(resolution,[],[f105,f357])).

fof(f357,plain,
    ( ! [X0,X1] : sP0(X0,X1,sK6,k2_funct_1(sK6))
    | ~ spl16_35 ),
    inference(unit_resulting_resolution,[],[f353,f65])).

fof(f65,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP1(X0,X1)
      | sP0(X4,X5,X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f105,plain,(
    ! [X2,X0,X3] :
      ( ~ sP0(X0,k1_funct_1(X3,X0),X2,X3)
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | r2_hidden(k1_funct_1(X3,X0),k1_relat_1(X2)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,k1_relat_1(X2))
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( k1_funct_1(X2,X1) != X0
            | ~ r2_hidden(X1,k1_relat_1(X2)) )
          & k1_funct_1(X3,X0) = X1
          & r2_hidden(X0,k2_relat_1(X2)) ) )
      & ( ( k1_funct_1(X2,X1) = X0
          & r2_hidden(X1,k1_relat_1(X2)) )
        | k1_funct_1(X3,X0) != X1
        | ~ r2_hidden(X0,k2_relat_1(X2))
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X2,X3,X0,X1] :
      ( ( sP0(X2,X3,X0,X1)
        | ( ( k1_funct_1(X0,X3) != X2
            | ~ r2_hidden(X3,k1_relat_1(X0)) )
          & k1_funct_1(X1,X2) = X3
          & r2_hidden(X2,k2_relat_1(X0)) ) )
      & ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0))
        | ~ sP0(X2,X3,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X3,X0,X1] :
      ( sP0(X2,X3,X0,X1)
    <=> ( ( k1_funct_1(X0,X3) = X2
          & r2_hidden(X3,k1_relat_1(X0)) )
        | k1_funct_1(X1,X2) != X3
        | ~ r2_hidden(X2,k2_relat_1(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f6415,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(sK6))
    | spl16_135 ),
    inference(avatar_component_clause,[],[f6414])).

fof(f8277,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | spl16_29
    | ~ spl16_133
    | ~ spl16_136
    | ~ spl16_149 ),
    inference(avatar_contradiction_clause,[],[f8276])).

fof(f8276,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | spl16_29
    | ~ spl16_133
    | ~ spl16_136
    | ~ spl16_149 ),
    inference(subsumption_resolution,[],[f8270,f6389])).

fof(f8270,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ spl16_1
    | ~ spl16_2
    | spl16_29
    | ~ spl16_136
    | ~ spl16_149 ),
    inference(unit_resulting_resolution,[],[f118,f123,f299,f6586,f8268,f2740])).

fof(f2740,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK13(X0,X1,X2),k2_relat_1(X0))
      | ~ r2_hidden(sK11(X0,sK13(X0,X1,X2)),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X2)
      | sP3(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f915])).

fof(f915,plain,(
    ! [X6,X8,X7,X9] :
      ( sK13(X6,X8,X9) != X7
      | sP3(X6,X8,X9)
      | ~ r2_hidden(sK11(X6,X7),X8)
      | ~ r2_hidden(sK13(X6,X8,X9),X9)
      | ~ r2_hidden(X7,k2_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(subsumption_resolution,[],[f911,f109])).

fof(f911,plain,(
    ! [X6,X8,X7,X9] :
      ( sK13(X6,X8,X9) != X7
      | sP3(X6,X8,X9)
      | ~ r2_hidden(sK11(X6,X7),X8)
      | ~ r2_hidden(sK11(X6,X7),k1_relat_1(X6))
      | ~ r2_hidden(sK13(X6,X8,X9),X9)
      | ~ r2_hidden(X7,k2_relat_1(X6))
      | ~ v1_funct_1(X6)
      | ~ v1_relat_1(X6) ) ),
    inference(superposition,[],[f98,f108])).

fof(f98,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X0,X4) != sK13(X0,X1,X2)
      | sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != sK13(X0,X1,X2)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(sK13(X0,X1,X2),X2) )
          & ( ( sK13(X0,X1,X2) = k1_funct_1(X0,sK14(X0,X1,X2))
              & r2_hidden(sK14(X0,X1,X2),X1)
              & r2_hidden(sK14(X0,X1,X2),k1_relat_1(X0)) )
            | r2_hidden(sK13(X0,X1,X2),X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ( k1_funct_1(X0,sK15(X0,X1,X6)) = X6
                & r2_hidden(sK15(X0,X1,X6),X1)
                & r2_hidden(sK15(X0,X1,X6),k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15])],[f51,f54,f53,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK13(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK13(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK13(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK13(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK13(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK13(X0,X1,X2) = k1_funct_1(X0,sK14(X0,X1,X2))
        & r2_hidden(sK14(X0,X1,X2),X1)
        & r2_hidden(sK14(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK15(X0,X1,X6)) = X6
        & r2_hidden(sK15(X0,X1,X6),X1)
        & r2_hidden(sK15(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X5] :
                  ( k1_funct_1(X0,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X5,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X2)
              | ! [X7] :
                  ( k1_funct_1(X0,X7) != X6
                  | ~ r2_hidden(X7,X1)
                  | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
            & ( ? [X8] :
                  ( k1_funct_1(X0,X8) = X6
                  & r2_hidden(X8,X1)
                  & r2_hidden(X8,k1_relat_1(X0)) )
              | ~ r2_hidden(X6,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ( ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4] :
                  ( k1_funct_1(X0,X4) != X3
                  | ~ r2_hidden(X4,X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
            & ( ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) )
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] :
              ( k1_funct_1(X0,X4) = X3
              & r2_hidden(X4,X1)
              & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f8268,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_149 ),
    inference(avatar_component_clause,[],[f8266])).

fof(f299,plain,
    ( ~ sP3(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))
    | spl16_29 ),
    inference(avatar_component_clause,[],[f297])).

fof(f297,plain,
    ( spl16_29
  <=> sP3(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_29])])).

fof(f8269,plain,
    ( spl16_149
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | spl16_134
    | ~ spl16_136 ),
    inference(avatar_split_clause,[],[f8245,f6584,f6391,f351,f149,f144,f138,f133,f121,f116,f8266])).

fof(f133,plain,
    ( spl16_4
  <=> sP4(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f144,plain,
    ( spl16_6
  <=> k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f6391,plain,
    ( spl16_134
  <=> r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_134])])).

fof(f8245,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | spl16_134
    | ~ spl16_136 ),
    inference(forward_demodulation,[],[f8239,f7569])).

fof(f8239,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | spl16_134 ),
    inference(unit_resulting_resolution,[],[f135,f140,f151,f146,f6392,f1201])).

fof(f1201,plain,(
    ! [X26,X24,X27,X25] :
      ( ~ sP4(X24)
      | k10_relat_1(X26,X27) = k9_relat_1(X24,X25)
      | r2_hidden(sK14(X24,X25,k10_relat_1(X26,X27)),X25)
      | r2_hidden(k1_funct_1(X26,sK13(X24,X25,k10_relat_1(X26,X27))),X27)
      | ~ v1_funct_1(X26)
      | ~ v1_relat_1(X26) ) ),
    inference(resolution,[],[f540,f111])).

fof(f540,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X2)
      | r2_hidden(sK14(X0,X1,X2),X1)
      | k9_relat_1(X0,X1) = X2
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f96,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | k9_relat_1(X0,X1) = X2
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ~ sP3(X0,X1,X2) )
          & ( sP3(X0,X1,X2)
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ sP4(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> sP3(X0,X1,X2) )
      | ~ sP4(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | r2_hidden(sK14(X0,X1,X2),X1)
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f6392,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),sK5)
    | spl16_134 ),
    inference(avatar_component_clause,[],[f6391])).

fof(f146,plain,
    ( k9_relat_1(sK6,sK5) != k10_relat_1(k2_funct_1(sK6),sK5)
    | spl16_6 ),
    inference(avatar_component_clause,[],[f144])).

fof(f135,plain,
    ( sP4(sK6)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f133])).

fof(f8230,plain,
    ( ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135
    | ~ spl16_136 ),
    inference(avatar_contradiction_clause,[],[f8229])).

fof(f8229,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f8228,f6586])).

fof(f8228,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(forward_demodulation,[],[f8227,f375])).

fof(f8227,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(subsumption_resolution,[],[f8226,f6393])).

fof(f6393,plain,
    ( r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),sK5)
    | ~ spl16_134 ),
    inference(avatar_component_clause,[],[f6391])).

fof(f8226,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_35
    | spl16_133
    | ~ spl16_135 ),
    inference(forward_demodulation,[],[f8225,f8212])).

fof(f8212,plain,
    ( sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))
    | ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | ~ spl16_135 ),
    inference(backward_demodulation,[],[f7470,f8203])).

fof(f8203,plain,
    ( sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(sK6,sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))
    | ~ spl16_4
    | spl16_6
    | spl16_133 ),
    inference(unit_resulting_resolution,[],[f135,f146,f6388,f697])).

fof(f697,plain,(
    ! [X2,X0,X1] :
      ( sK13(X0,X1,X2) = k1_funct_1(X0,sK14(X0,X1,X2))
      | r2_hidden(sK13(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f97,f90])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | sK13(X0,X1,X2) = k1_funct_1(X0,sK14(X0,X1,X2))
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f6388,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | spl16_133 ),
    inference(avatar_component_clause,[],[f6387])).

fof(f7470,plain,
    ( sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))))
    | ~ spl16_35
    | ~ spl16_135 ),
    inference(unit_resulting_resolution,[],[f353,f6416,f101])).

fof(f6416,plain,
    ( r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(sK6))
    | ~ spl16_135 ),
    inference(avatar_component_clause,[],[f6414])).

fof(f8225,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_133 ),
    inference(subsumption_resolution,[],[f8224,f140])).

fof(f8224,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_7
    | spl16_133 ),
    inference(subsumption_resolution,[],[f8210,f151])).

fof(f8210,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl16_133 ),
    inference(resolution,[],[f6388,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8108,plain,
    ( spl16_148
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_147 ),
    inference(avatar_split_clause,[],[f8080,f8057,f373,f149,f138,f8105])).

fof(f8105,plain,
    ( spl16_148
  <=> r2_hidden(sK11(k2_funct_1(sK6),sK9(k2_funct_1(sK6),k1_relat_1(sK6))),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_148])])).

fof(f8057,plain,
    ( spl16_147
  <=> r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k2_relat_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_147])])).

fof(f8080,plain,
    ( r2_hidden(sK11(k2_funct_1(sK6),sK9(k2_funct_1(sK6),k1_relat_1(sK6))),k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_147 ),
    inference(forward_demodulation,[],[f8067,f375])).

fof(f8067,plain,
    ( r2_hidden(sK11(k2_funct_1(sK6),sK9(k2_funct_1(sK6),k1_relat_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_147 ),
    inference(unit_resulting_resolution,[],[f140,f151,f8059,f109])).

fof(f8059,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_147 ),
    inference(avatar_component_clause,[],[f8057])).

fof(f8060,plain,
    ( spl16_147
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_146 ),
    inference(avatar_split_clause,[],[f8001,f7974,f157,f149,f138,f8057])).

fof(f157,plain,
    ( spl16_8
  <=> sP4(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_8])])).

fof(f7974,plain,
    ( spl16_146
  <=> r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_146])])).

fof(f8001,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_146 ),
    inference(unit_resulting_resolution,[],[f140,f151,f226,f7976,f505])).

fof(f505,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,X3)
      | ~ sP3(X0,X1,X3) ) ),
    inference(subsumption_resolution,[],[f503,f91])).

fof(f91,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK15(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f503,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k2_relat_1(X0))
      | ~ r2_hidden(sK15(X0,X1,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,X3)
      | ~ sP3(X0,X1,X3) ) ),
    inference(superposition,[],[f107,f93])).

fof(f93,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK15(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7976,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_146 ),
    inference(avatar_component_clause,[],[f7974])).

fof(f226,plain,
    ( ! [X0] : sP3(k2_funct_1(sK6),X0,k9_relat_1(k2_funct_1(sK6),X0))
    | ~ spl16_8 ),
    inference(unit_resulting_resolution,[],[f159,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1,k9_relat_1(X0,X1))
      | ~ sP4(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ sP4(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f159,plain,
    ( sP4(k2_funct_1(sK6))
    | ~ spl16_8 ),
    inference(avatar_component_clause,[],[f157])).

fof(f7977,plain,
    ( spl16_146
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_109
    | ~ spl16_141 ),
    inference(avatar_split_clause,[],[f7847,f7812,f2464,f373,f351,f157,f7974])).

fof(f2464,plain,
    ( spl16_109
  <=> r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_109])])).

fof(f7812,plain,
    ( spl16_141
  <=> r2_hidden(k1_funct_1(sK6,sK9(k2_funct_1(sK6),k1_relat_1(sK6))),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_141])])).

fof(f7847,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_109
    | ~ spl16_141 ),
    inference(forward_demodulation,[],[f7842,f7417])).

fof(f7417,plain,
    ( sK9(k2_funct_1(sK6),k1_relat_1(sK6)) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK9(k2_funct_1(sK6),k1_relat_1(sK6))))
    | ~ spl16_35
    | ~ spl16_109 ),
    inference(unit_resulting_resolution,[],[f353,f2466,f101])).

fof(f2466,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6))
    | ~ spl16_109 ),
    inference(avatar_component_clause,[],[f2464])).

fof(f7842,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK9(k2_funct_1(sK6),k1_relat_1(sK6)))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_141 ),
    inference(unit_resulting_resolution,[],[f7814,f7814,f1642])).

fof(f1642,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),X0),k9_relat_1(k2_funct_1(sK6),X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(sK6)) )
    | ~ spl16_8
    | ~ spl16_38 ),
    inference(resolution,[],[f558,f226])).

fof(f558,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP3(k2_funct_1(sK6),X1,X2)
        | ~ r2_hidden(X0,X1)
        | r2_hidden(k1_funct_1(k2_funct_1(sK6),X0),X2)
        | ~ r2_hidden(X0,k2_relat_1(sK6)) )
    | ~ spl16_38 ),
    inference(superposition,[],[f114,f375])).

fof(f114,plain,(
    ! [X2,X0,X7,X1] :
      ( ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ r2_hidden(X7,X1)
      | r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f7814,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9(k2_funct_1(sK6),k1_relat_1(sK6))),k2_relat_1(sK6))
    | ~ spl16_141 ),
    inference(avatar_component_clause,[],[f7812])).

fof(f7925,plain,
    ( ~ spl16_145
    | ~ spl16_4
    | spl16_79
    | ~ spl16_82
    | ~ spl16_139 ),
    inference(avatar_split_clause,[],[f7647,f7609,f1013,f963,f133,f7922])).

fof(f7922,plain,
    ( spl16_145
  <=> r2_hidden(sK15(sK6,k1_relat_1(sK6),sK13(sK6,sK5,k2_relat_1(sK6))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_145])])).

fof(f963,plain,
    ( spl16_79
  <=> sP3(sK6,sK5,k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_79])])).

fof(f1013,plain,
    ( spl16_82
  <=> r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_82])])).

fof(f7609,plain,
    ( spl16_139
  <=> r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k1_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_139])])).

fof(f7647,plain,
    ( ~ r2_hidden(sK15(sK6,k1_relat_1(sK6),sK13(sK6,sK5,k2_relat_1(sK6))),sK5)
    | ~ spl16_4
    | spl16_79
    | ~ spl16_82
    | ~ spl16_139 ),
    inference(unit_resulting_resolution,[],[f965,f225,f1015,f7611,f2686])).

fof(f2686,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X0,X3,X4)
      | ~ r2_hidden(sK15(X0,X3,sK13(X0,X1,X2)),X1)
      | ~ r2_hidden(sK13(X0,X1,X2),X2)
      | ~ r2_hidden(sK13(X0,X1,X2),X4)
      | sP3(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f914])).

fof(f914,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK13(X0,X3,X4) != X2
      | sP3(X0,X3,X4)
      | ~ r2_hidden(sK15(X0,X1,X2),X3)
      | ~ r2_hidden(sK13(X0,X3,X4),X4)
      | ~ r2_hidden(X2,X5)
      | ~ sP3(X0,X1,X5) ) ),
    inference(subsumption_resolution,[],[f910,f91])).

fof(f910,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sK13(X0,X3,X4) != X2
      | sP3(X0,X3,X4)
      | ~ r2_hidden(sK15(X0,X1,X2),X3)
      | ~ r2_hidden(sK15(X0,X1,X2),k1_relat_1(X0))
      | ~ r2_hidden(sK13(X0,X3,X4),X4)
      | ~ r2_hidden(X2,X5)
      | ~ sP3(X0,X1,X5) ) ),
    inference(superposition,[],[f98,f93])).

fof(f7611,plain,
    ( r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ spl16_139 ),
    inference(avatar_component_clause,[],[f7609])).

fof(f1015,plain,
    ( r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | ~ spl16_82 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f225,plain,
    ( ! [X0] : sP3(sK6,X0,k9_relat_1(sK6,X0))
    | ~ spl16_4 ),
    inference(unit_resulting_resolution,[],[f135,f113])).

fof(f965,plain,
    ( ~ sP3(sK6,sK5,k2_relat_1(sK6))
    | spl16_79 ),
    inference(avatar_component_clause,[],[f963])).

fof(f7914,plain,
    ( ~ spl16_144
    | ~ spl16_4
    | spl16_89 ),
    inference(avatar_split_clause,[],[f7896,f1377,f133,f7911])).

fof(f7911,plain,
    ( spl16_144
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_144])])).

fof(f1377,plain,
    ( spl16_89
  <=> r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_89])])).

fof(f7896,plain,
    ( ~ r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,sK5))
    | ~ spl16_4
    | spl16_89 ),
    inference(unit_resulting_resolution,[],[f225,f1378,f92])).

fof(f92,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK15(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1378,plain,
    ( ~ r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),sK5)
    | spl16_89 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f7906,plain,
    ( ~ spl16_143
    | spl16_89
    | ~ spl16_90 ),
    inference(avatar_split_clause,[],[f7898,f1402,f1377,f7903])).

fof(f7903,plain,
    ( spl16_143
  <=> sP3(sK6,sK5,k9_relat_1(sK6,k1_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_143])])).

fof(f1402,plain,
    ( spl16_90
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k1_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_90])])).

fof(f7898,plain,
    ( ~ sP3(sK6,sK5,k9_relat_1(sK6,k1_relat_1(sK6)))
    | spl16_89
    | ~ spl16_90 ),
    inference(unit_resulting_resolution,[],[f1404,f1378,f92])).

fof(f1404,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ spl16_90 ),
    inference(avatar_component_clause,[],[f1402])).

fof(f7876,plain,
    ( spl16_142
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_109
    | ~ spl16_141 ),
    inference(avatar_split_clause,[],[f7816,f7812,f2464,f121,f116,f7873])).

fof(f7873,plain,
    ( spl16_142
  <=> r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k10_relat_1(sK6,k2_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_142])])).

fof(f7816,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k10_relat_1(sK6,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_109
    | ~ spl16_141 ),
    inference(unit_resulting_resolution,[],[f118,f123,f2466,f7814,f110])).

fof(f7815,plain,
    ( spl16_141
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_109 ),
    inference(avatar_split_clause,[],[f7420,f2464,f121,f116,f7812])).

fof(f7420,plain,
    ( r2_hidden(k1_funct_1(sK6,sK9(k2_funct_1(sK6),k1_relat_1(sK6))),k2_relat_1(sK6))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_109 ),
    inference(unit_resulting_resolution,[],[f118,f123,f2466,f107])).

fof(f7760,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(avatar_contradiction_clause,[],[f7759])).

fof(f7759,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(subsumption_resolution,[],[f7758,f1338])).

fof(f1338,plain,
    ( ! [X0] : ~ r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),X0))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_88 ),
    inference(unit_resulting_resolution,[],[f226,f151,f140,f1331,f505])).

fof(f1331,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(k2_funct_1(sK6)))
    | spl16_88 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f1329,plain,
    ( spl16_88
  <=> r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_88])])).

fof(f7758,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | ~ spl16_140 ),
    inference(forward_demodulation,[],[f7703,f7400])).

fof(f7400,plain,
    ( sK14(sK6,sK5,k2_relat_1(sK6)) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6))))
    | ~ spl16_35
    | ~ spl16_87 ),
    inference(unit_resulting_resolution,[],[f353,f1232,f101])).

fof(f1232,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k1_relat_1(sK6))
    | ~ spl16_87 ),
    inference(avatar_component_clause,[],[f1230])).

fof(f1230,plain,
    ( spl16_87
  <=> r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_87])])).

fof(f7703,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6)))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_140 ),
    inference(unit_resulting_resolution,[],[f226,f7698,f7698,f558])).

fof(f7698,plain,
    ( r2_hidden(k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6))),k2_relat_1(sK6))
    | ~ spl16_140 ),
    inference(avatar_component_clause,[],[f7696])).

fof(f7696,plain,
    ( spl16_140
  <=> r2_hidden(k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6))),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_140])])).

fof(f7749,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(avatar_contradiction_clause,[],[f7748])).

fof(f7748,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(subsumption_resolution,[],[f7747,f1338])).

fof(f7747,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | ~ spl16_140 ),
    inference(forward_demodulation,[],[f7712,f7400])).

fof(f7712,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6)))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_140 ),
    inference(unit_resulting_resolution,[],[f7698,f7698,f1642])).

fof(f7738,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(avatar_contradiction_clause,[],[f7737])).

fof(f7737,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(subsumption_resolution,[],[f7736,f1338])).

fof(f7736,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | ~ spl16_140 ),
    inference(forward_demodulation,[],[f7725,f7400])).

fof(f7725,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6)))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_140 ),
    inference(unit_resulting_resolution,[],[f226,f7698,f7698,f558])).

fof(f7735,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(avatar_contradiction_clause,[],[f7734])).

fof(f7734,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | spl16_88
    | ~ spl16_140 ),
    inference(subsumption_resolution,[],[f7733,f1338])).

fof(f7733,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_87
    | ~ spl16_140 ),
    inference(forward_demodulation,[],[f7726,f7400])).

fof(f7726,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6)))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_140 ),
    inference(unit_resulting_resolution,[],[f7698,f7698,f1642])).

fof(f7699,plain,
    ( spl16_140
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_87 ),
    inference(avatar_split_clause,[],[f7403,f1230,f121,f116,f7696])).

fof(f7403,plain,
    ( r2_hidden(k1_funct_1(sK6,sK14(sK6,sK5,k2_relat_1(sK6))),k2_relat_1(sK6))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_87 ),
    inference(unit_resulting_resolution,[],[f118,f123,f1232,f107])).

fof(f7612,plain,
    ( spl16_139
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_82 ),
    inference(avatar_split_clause,[],[f7365,f1013,f121,f116,f7609])).

fof(f7365,plain,
    ( r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_82 ),
    inference(unit_resulting_resolution,[],[f118,f123,f1015,f3855])).

fof(f3855,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | r2_hidden(X1,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f3852])).

fof(f3852,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f3592,f108])).

fof(f3592,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X0,sK11(X0,X1)),k9_relat_1(X0,k1_relat_1(X0)))
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f3579,f99])).

fof(f99,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( sP4(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f19,f25,f24])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f3579,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X0,sK11(X0,X1)),k9_relat_1(X0,k1_relat_1(X0)))
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f1617,f113])).

fof(f1617,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,k1_relat_1(X0),X2)
      | r2_hidden(k1_funct_1(X0,sK11(X0,X1)),X2)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f1606])).

fof(f1606,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,sK11(X0,X1)),X2)
      | ~ sP3(X0,k1_relat_1(X0),X2)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f555,f109])).

fof(f555,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK11(X0,X1),X2)
      | r2_hidden(k1_funct_1(X0,sK11(X0,X1)),X3)
      | ~ sP3(X0,X2,X3)
      | ~ r2_hidden(X1,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f114,f109])).

fof(f7607,plain,
    ( spl16_138
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_82 ),
    inference(avatar_split_clause,[],[f7361,f1013,f121,f116,f7604])).

fof(f7604,plain,
    ( spl16_138
  <=> r2_hidden(sK11(sK6,sK13(sK6,sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_138])])).

fof(f7361,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_82 ),
    inference(unit_resulting_resolution,[],[f118,f123,f1015,f109])).

fof(f7513,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | spl16_6
    | spl16_133
    | spl16_136 ),
    inference(avatar_contradiction_clause,[],[f7512])).

fof(f7512,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | spl16_6
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7511,f146])).

fof(f7511,plain,
    ( k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7510,f6388])).

fof(f7510,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7509,f118])).

fof(f7509,plain,
    ( ~ v1_relat_1(sK6)
    | r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5)
    | ~ spl16_2
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7495,f123])).

fof(f7495,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5)
    | spl16_136 ),
    inference(resolution,[],[f6585,f1810])).

fof(f1810,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK13(X13,X14,X15),k2_relat_1(X13))
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13)
      | r2_hidden(sK13(X13,X14,X15),X15)
      | k9_relat_1(X13,X14) = X15 ) ),
    inference(subsumption_resolution,[],[f1809,f99])).

fof(f1809,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK13(X13,X14,X15),k2_relat_1(X13))
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13)
      | r2_hidden(sK13(X13,X14,X15),X15)
      | k9_relat_1(X13,X14) = X15
      | ~ sP4(X13) ) ),
    inference(subsumption_resolution,[],[f1799,f575])).

fof(f575,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK14(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK13(X0,X1,X2),X2)
      | k9_relat_1(X0,X1) = X2
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f95,f90])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | r2_hidden(sK14(X0,X1,X2),k1_relat_1(X0))
      | r2_hidden(sK13(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1799,plain,(
    ! [X14,X15,X13] :
      ( r2_hidden(sK13(X13,X14,X15),k2_relat_1(X13))
      | ~ r2_hidden(sK14(X13,X14,X15),k1_relat_1(X13))
      | ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13)
      | r2_hidden(sK13(X13,X14,X15),X15)
      | k9_relat_1(X13,X14) = X15
      | ~ sP4(X13) ) ),
    inference(superposition,[],[f107,f697])).

fof(f6585,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | spl16_136 ),
    inference(avatar_component_clause,[],[f6584])).

fof(f7508,plain,
    ( ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(avatar_contradiction_clause,[],[f7507])).

fof(f7507,plain,
    ( $false
    | ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7506,f146])).

fof(f7506,plain,
    ( k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5)
    | ~ spl16_4
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7494,f6388])).

fof(f7494,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | k9_relat_1(sK6,sK5) = k10_relat_1(k2_funct_1(sK6),sK5)
    | ~ spl16_4
    | ~ spl16_35
    | spl16_136 ),
    inference(resolution,[],[f6585,f4475])).

fof(f4475,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK13(sK6,X0,X1),k2_relat_1(sK6))
        | r2_hidden(sK13(sK6,X0,X1),X1)
        | k9_relat_1(sK6,X0) = X1 )
    | ~ spl16_4
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f4474,f135])).

fof(f4474,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK13(sK6,X0,X1),k2_relat_1(sK6))
        | r2_hidden(sK13(sK6,X0,X1),X1)
        | k9_relat_1(sK6,X0) = X1
        | ~ sP4(sK6) )
    | ~ spl16_35 ),
    inference(resolution,[],[f1811,f353])).

fof(f1811,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ sP1(X19,X16)
      | r2_hidden(sK13(X16,X17,X18),k2_relat_1(X16))
      | r2_hidden(sK13(X16,X17,X18),X18)
      | k9_relat_1(X16,X17) = X18
      | ~ sP4(X16) ) ),
    inference(subsumption_resolution,[],[f1800,f575])).

fof(f1800,plain,(
    ! [X19,X17,X18,X16] :
      ( r2_hidden(sK13(X16,X17,X18),k2_relat_1(X16))
      | ~ r2_hidden(sK14(X16,X17,X18),k1_relat_1(X16))
      | ~ sP1(X19,X16)
      | r2_hidden(sK13(X16,X17,X18),X18)
      | k9_relat_1(X16,X17) = X18
      | ~ sP4(X16) ) ),
    inference(superposition,[],[f102,f697])).

fof(f102,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k1_funct_1(X1,X5),k2_relat_1(X1))
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP1(X0,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,k2_relat_1(X1))
      | k1_funct_1(X1,X5) != X4
      | ~ r2_hidden(X5,k1_relat_1(X1))
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7505,plain,
    ( ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(avatar_contradiction_clause,[],[f7504])).

fof(f7504,plain,
    ( $false
    | ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7488,f6388])).

fof(f7488,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_136 ),
    inference(unit_resulting_resolution,[],[f146,f6585,f4475])).

fof(f7503,plain,
    ( ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(avatar_contradiction_clause,[],[f7502])).

fof(f7502,plain,
    ( $false
    | ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7489,f6388])).

fof(f7489,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ spl16_4
    | spl16_6
    | ~ spl16_35
    | spl16_136 ),
    inference(unit_resulting_resolution,[],[f135,f353,f146,f6585,f1811])).

fof(f7501,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | spl16_6
    | spl16_133
    | spl16_136 ),
    inference(avatar_contradiction_clause,[],[f7500])).

fof(f7500,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | spl16_6
    | spl16_133
    | spl16_136 ),
    inference(subsumption_resolution,[],[f7490,f6388])).

fof(f7490,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ spl16_1
    | ~ spl16_2
    | spl16_6
    | spl16_136 ),
    inference(unit_resulting_resolution,[],[f118,f123,f146,f6585,f1810])).

fof(f7313,plain,
    ( ~ spl16_137
    | spl16_108 ),
    inference(avatar_split_clause,[],[f7308,f2460,f7310])).

fof(f7310,plain,
    ( spl16_137
  <=> sP1(sK6,k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_137])])).

fof(f2460,plain,
    ( spl16_108
  <=> k1_relat_1(sK6) = k2_relat_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_108])])).

fof(f7308,plain,
    ( ~ sP1(sK6,k2_funct_1(sK6))
    | spl16_108 ),
    inference(unit_resulting_resolution,[],[f2461,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | k1_relat_1(X0) = k2_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2461,plain,
    ( k1_relat_1(sK6) != k2_relat_1(k2_funct_1(sK6))
    | spl16_108 ),
    inference(avatar_component_clause,[],[f2460])).

fof(f7304,plain,
    ( ~ spl16_4
    | spl16_79
    | ~ spl16_81 ),
    inference(avatar_contradiction_clause,[],[f7303])).

fof(f7303,plain,
    ( $false
    | ~ spl16_4
    | spl16_79
    | ~ spl16_81 ),
    inference(subsumption_resolution,[],[f7302,f135])).

fof(f7302,plain,
    ( ~ sP4(sK6)
    | spl16_79
    | ~ spl16_81 ),
    inference(subsumption_resolution,[],[f7298,f965])).

fof(f7298,plain,
    ( sP3(sK6,sK5,k2_relat_1(sK6))
    | ~ sP4(sK6)
    | ~ spl16_81 ),
    inference(superposition,[],[f113,f1008])).

fof(f1008,plain,
    ( k9_relat_1(sK6,sK5) = k2_relat_1(sK6)
    | ~ spl16_81 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1007,plain,
    ( spl16_81
  <=> k9_relat_1(sK6,sK5) = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_81])])).

fof(f7300,plain,
    ( ~ spl16_4
    | spl16_79
    | ~ spl16_81 ),
    inference(avatar_contradiction_clause,[],[f7299])).

fof(f7299,plain,
    ( $false
    | ~ spl16_4
    | spl16_79
    | ~ spl16_81 ),
    inference(subsumption_resolution,[],[f7289,f965])).

fof(f7289,plain,
    ( sP3(sK6,sK5,k2_relat_1(sK6))
    | ~ spl16_4
    | ~ spl16_81 ),
    inference(superposition,[],[f225,f1008])).

fof(f7288,plain,
    ( spl16_81
    | ~ spl16_4
    | ~ spl16_35
    | spl16_82 ),
    inference(avatar_split_clause,[],[f4484,f1013,f351,f133,f1007])).

fof(f4484,plain,
    ( k9_relat_1(sK6,sK5) = k2_relat_1(sK6)
    | ~ spl16_4
    | ~ spl16_35
    | spl16_82 ),
    inference(resolution,[],[f4482,f1014])).

fof(f1014,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | spl16_82 ),
    inference(avatar_component_clause,[],[f1013])).

fof(f4482,plain,
    ( ! [X0] :
        ( r2_hidden(sK13(sK6,X0,k2_relat_1(sK6)),k2_relat_1(sK6))
        | k9_relat_1(sK6,X0) = k2_relat_1(sK6) )
    | ~ spl16_4
    | ~ spl16_35 ),
    inference(factoring,[],[f4475])).

fof(f7257,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | spl16_95
    | ~ spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7256])).

fof(f7256,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | spl16_95
    | ~ spl16_110 ),
    inference(subsumption_resolution,[],[f7255,f1652])).

fof(f1652,plain,
    ( ~ r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | spl16_95 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f1651,plain,
    ( spl16_95
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_95])])).

fof(f7255,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_110 ),
    inference(forward_demodulation,[],[f1640,f2983])).

fof(f2983,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_110 ),
    inference(avatar_component_clause,[],[f2981])).

fof(f2981,plain,
    ( spl16_110
  <=> k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_110])])).

fof(f1640,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f969,f969,f226,f558])).

fof(f969,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | ~ spl16_80 ),
    inference(avatar_component_clause,[],[f967])).

fof(f967,plain,
    ( spl16_80
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_80])])).

fof(f7254,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90
    | spl16_101
    | ~ spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7253])).

fof(f7253,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90
    | spl16_101
    | ~ spl16_110 ),
    inference(subsumption_resolution,[],[f7252,f2002])).

fof(f2002,plain,
    ( ~ r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | spl16_101 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f2001,plain,
    ( spl16_101
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_101])])).

fof(f7252,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90
    | ~ spl16_110 ),
    inference(forward_demodulation,[],[f1641,f2983])).

fof(f1641,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90 ),
    inference(unit_resulting_resolution,[],[f1404,f969,f226,f558])).

fof(f7215,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_101
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(avatar_contradiction_clause,[],[f7214])).

fof(f7214,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_101
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f7016,f2002])).

fof(f7016,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(forward_demodulation,[],[f2202,f7005])).

fof(f7005,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(backward_demodulation,[],[f7003,f2203])).

fof(f2203,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_104 ),
    inference(unit_resulting_resolution,[],[f225,f2197,f93])).

fof(f2197,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)))))
    | ~ spl16_104 ),
    inference(avatar_component_clause,[],[f2195])).

fof(f2195,plain,
    ( spl16_104
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_104])])).

fof(f7003,plain,
    ( sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,k1_funct_1(sK6,sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_112 ),
    inference(forward_demodulation,[],[f3203,f3205])).

fof(f3205,plain,
    ( sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_35
    | ~ spl16_112 ),
    inference(resolution,[],[f3161,f428])).

fof(f3161,plain,
    ( r2_hidden(sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_112 ),
    inference(avatar_component_clause,[],[f3159])).

fof(f3159,plain,
    ( spl16_112
  <=> r2_hidden(sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_112])])).

fof(f3203,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))) = sK11(sK6,k1_funct_1(sK6,sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_112 ),
    inference(resolution,[],[f3161,f726])).

fof(f2202,plain,
    ( r2_hidden(sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_104 ),
    inference(unit_resulting_resolution,[],[f225,f2197,f92])).

fof(f7213,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90
    | ~ spl16_99
    | spl16_101
    | ~ spl16_111 ),
    inference(avatar_contradiction_clause,[],[f7212])).

fof(f7212,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90
    | ~ spl16_99
    | spl16_101
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f2002,f7171])).

fof(f7171,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_90
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(backward_demodulation,[],[f1641,f7167])).

fof(f7167,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(forward_demodulation,[],[f6782,f6802])).

fof(f6802,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(forward_demodulation,[],[f1845,f3012])).

fof(f3012,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_111 ),
    inference(avatar_component_clause,[],[f3010])).

fof(f3010,plain,
    ( spl16_111
  <=> sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_111])])).

fof(f1845,plain,
    ( sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = k1_funct_1(sK6,sK11(sK6,sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_99 ),
    inference(unit_resulting_resolution,[],[f118,f123,f1825,f108])).

fof(f1825,plain,
    ( r2_hidden(sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_99 ),
    inference(avatar_component_clause,[],[f1823])).

fof(f1823,plain,
    ( spl16_99
  <=> r2_hidden(sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_99])])).

fof(f6782,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(forward_demodulation,[],[f1835,f3012])).

fof(f1835,plain,
    ( sK11(sK6,sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99 ),
    inference(unit_resulting_resolution,[],[f1825,f463])).

fof(f7177,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | spl16_95
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(avatar_contradiction_clause,[],[f7176])).

fof(f7176,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | spl16_95
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f7170,f1652])).

fof(f7170,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(backward_demodulation,[],[f1640,f7167])).

fof(f7161,plain,
    ( ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | spl16_102 ),
    inference(avatar_contradiction_clause,[],[f7160])).

fof(f7160,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | spl16_102 ),
    inference(subsumption_resolution,[],[f7159,f7091])).

fof(f7091,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f2013,f2795])).

fof(f2795,plain,
    ( k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = sK15(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f2003,f226,f2793])).

fof(f2793,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP3(k2_funct_1(sK6),X2,X1)
        | k1_funct_1(sK6,X0) = sK15(k2_funct_1(sK6),X2,X0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f2790,f357])).

fof(f2790,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ sP0(sK15(k2_funct_1(sK6),X2,X0),X0,sK6,k2_funct_1(sK6))
        | k1_funct_1(sK6,X0) = sK15(k2_funct_1(sK6),X2,X0)
        | ~ sP3(k2_funct_1(sK6),X2,X1) )
    | ~ spl16_38 ),
    inference(duplicate_literal_removal,[],[f2789])).

fof(f2789,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ sP0(sK15(k2_funct_1(sK6),X2,X0),X0,sK6,k2_funct_1(sK6))
        | k1_funct_1(sK6,X0) = sK15(k2_funct_1(sK6),X2,X0)
        | ~ sP3(k2_funct_1(sK6),X2,X1)
        | ~ sP3(k2_funct_1(sK6),X2,X1) )
    | ~ spl16_38 ),
    inference(condensation,[],[f2783])).

fof(f2783,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ sP0(sK15(k2_funct_1(sK6),X5,X6),X6,sK6,k2_funct_1(sK6))
        | k1_funct_1(sK6,X6) = sK15(k2_funct_1(sK6),X5,X6)
        | ~ r2_hidden(X6,X7)
        | ~ sP3(k2_funct_1(sK6),X5,X7)
        | ~ r2_hidden(X6,X8)
        | ~ sP3(k2_funct_1(sK6),X5,X8) )
    | ~ spl16_38 ),
    inference(resolution,[],[f619,f414])).

fof(f414,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK15(k2_funct_1(sK6),X0,X1),k2_relat_1(sK6))
        | ~ r2_hidden(X1,X2)
        | ~ sP3(k2_funct_1(sK6),X0,X2) )
    | ~ spl16_38 ),
    inference(superposition,[],[f91,f375])).

fof(f619,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(sK15(X0,X1,X2),k2_relat_1(X3))
      | ~ sP0(sK15(X0,X1,X2),X2,X3,X0)
      | sK15(X0,X1,X2) = k1_funct_1(X3,X2)
      | ~ r2_hidden(X2,X4)
      | ~ sP3(X0,X1,X4) ) ),
    inference(superposition,[],[f104,f93])).

fof(f104,plain,(
    ! [X2,X0,X3] :
      ( ~ sP0(X0,k1_funct_1(X3,X0),X2,X3)
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | k1_funct_1(X2,k1_funct_1(X3,X0)) = X0 ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) = X0
      | k1_funct_1(X3,X0) != X1
      | ~ r2_hidden(X0,k2_relat_1(X2))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2003,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_101 ),
    inference(avatar_component_clause,[],[f2001])).

fof(f2013,plain,
    ( r2_hidden(sK15(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f226,f2003,f414])).

fof(f7159,plain,
    ( ~ r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | spl16_102 ),
    inference(backward_demodulation,[],[f2039,f4862])).

fof(f4862,plain,
    ( k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f2003,f4812])).

fof(f4812,plain,
    ( ! [X4,X5] :
        ( k1_funct_1(sK6,X4) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),X4)
        | ~ r2_hidden(X4,k9_relat_1(k2_funct_1(sK6),X5)) )
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(resolution,[],[f4804,f2796])).

fof(f2796,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(k2_funct_1(sK6),X1))
        | k1_funct_1(sK6,X0) = sK15(k2_funct_1(sK6),X1,X0) )
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(resolution,[],[f2793,f226])).

fof(f4804,plain,
    ( ! [X6,X5] :
        ( r2_hidden(X5,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X5,k9_relat_1(k2_funct_1(sK6),X6)) )
    | ~ spl16_8
    | ~ spl16_38 ),
    inference(forward_demodulation,[],[f4784,f375])).

fof(f4784,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k9_relat_1(k2_funct_1(sK6),X6))
        | r2_hidden(X5,k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6)))) )
    | ~ spl16_8 ),
    inference(resolution,[],[f4754,f159])).

fof(f4754,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | r2_hidden(X1,k9_relat_1(X0,k1_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f4742])).

fof(f4742,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0)
      | ~ r2_hidden(X1,k9_relat_1(X0,X2))
      | r2_hidden(X1,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f4727,f113])).

fof(f4727,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X0,X1,X3)
      | ~ sP4(X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k9_relat_1(X0,k1_relat_1(X0))) ) ),
    inference(subsumption_resolution,[],[f4696,f3445])).

fof(f3445,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X2,X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X3))
      | ~ r2_hidden(X0,X1)
      | ~ sP4(X2) ) ),
    inference(duplicate_literal_removal,[],[f3444])).

fof(f3444,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k9_relat_1(X2,X3))
      | ~ sP3(X2,X3,X1)
      | ~ sP4(X2)
      | ~ sP3(X2,X3,X1) ) ),
    inference(condensation,[],[f3442])).

fof(f3442,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X2,k9_relat_1(X0,X1))
      | ~ r2_hidden(X2,X3)
      | ~ sP3(X0,X1,X3)
      | ~ sP4(X0)
      | ~ r2_hidden(X2,X4)
      | ~ sP3(X0,X1,X4) ) ),
    inference(superposition,[],[f3315,f93])).

fof(f3315,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,sK15(X0,X1,X2)),k9_relat_1(X0,X1))
      | ~ r2_hidden(X2,X3)
      | ~ sP3(X0,X1,X3)
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f1975,f113])).

fof(f1975,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X2,X3,X4)
      | r2_hidden(k1_funct_1(X2,sK15(X2,X3,X0)),X4)
      | ~ r2_hidden(X0,X1)
      | ~ sP3(X2,X3,X1) ) ),
    inference(duplicate_literal_removal,[],[f1974])).

fof(f1974,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k1_funct_1(X2,sK15(X2,X3,X0)),X4)
      | ~ sP3(X2,X3,X4)
      | ~ sP3(X2,X3,X1)
      | ~ sP3(X2,X3,X1) ) ),
    inference(condensation,[],[f1958])).

fof(f1958,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k1_funct_1(X0,sK15(X0,X1,X2)),X3)
      | ~ sP3(X0,X1,X3)
      | ~ r2_hidden(X2,X4)
      | ~ sP3(X0,X1,X4)
      | ~ r2_hidden(X2,X5)
      | ~ sP3(X0,X1,X5) ) ),
    inference(resolution,[],[f556,f92])).

fof(f556,plain,(
    ! [X6,X4,X8,X7,X5,X9] :
      ( ~ r2_hidden(sK15(X4,X5,X6),X7)
      | r2_hidden(k1_funct_1(X4,sK15(X4,X5,X6)),X8)
      | ~ sP3(X4,X7,X8)
      | ~ r2_hidden(X6,X9)
      | ~ sP3(X4,X5,X9) ) ),
    inference(resolution,[],[f114,f91])).

fof(f4696,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k9_relat_1(X0,k1_relat_1(X0)))
      | ~ r2_hidden(X2,k9_relat_1(X0,X1))
      | ~ sP4(X0)
      | ~ r2_hidden(X2,X3)
      | ~ sP3(X0,X1,X3) ) ),
    inference(superposition,[],[f4644,f93])).

fof(f4644,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,sK15(X1,X2,X0)),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ sP4(X1) ) ),
    inference(duplicate_literal_removal,[],[f4632])).

fof(f4632,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | r2_hidden(k1_funct_1(X1,sK15(X1,X2,X0)),k9_relat_1(X1,k1_relat_1(X1)))
      | ~ sP4(X1)
      | ~ sP4(X1) ) ),
    inference(resolution,[],[f3672,f113])).

fof(f3672,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X0,X1,X3)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(k1_funct_1(X0,sK15(X0,X1,X2)),k9_relat_1(X0,k1_relat_1(X0)))
      | ~ sP4(X0) ) ),
    inference(resolution,[],[f1973,f113])).

fof(f1973,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X2,k1_relat_1(X2),X4)
      | r2_hidden(k1_funct_1(X2,sK15(X2,X3,X0)),X4)
      | ~ r2_hidden(X0,X1)
      | ~ sP3(X2,X3,X1) ) ),
    inference(duplicate_literal_removal,[],[f1972])).

fof(f1972,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(k1_funct_1(X2,sK15(X2,X3,X0)),X4)
      | ~ sP3(X2,k1_relat_1(X2),X4)
      | ~ sP3(X2,X3,X1)
      | ~ sP3(X2,X3,X1) ) ),
    inference(condensation,[],[f1959])).

fof(f1959,plain,(
    ! [X6,X10,X8,X7,X11,X9] :
      ( r2_hidden(k1_funct_1(X6,sK15(X6,X7,X8)),X9)
      | ~ sP3(X6,k1_relat_1(X6),X9)
      | ~ r2_hidden(X8,X10)
      | ~ sP3(X6,X7,X10)
      | ~ r2_hidden(X8,X11)
      | ~ sP3(X6,X7,X11) ) ),
    inference(resolution,[],[f556,f91])).

fof(f2039,plain,
    ( ~ r2_hidden(sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | spl16_102 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f2038,plain,
    ( spl16_102
  <=> r2_hidden(sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_102])])).

fof(f7158,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7157])).

fof(f7157,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110 ),
    inference(subsumption_resolution,[],[f2212,f2982])).

fof(f2982,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) != sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | spl16_110 ),
    inference(avatar_component_clause,[],[f2981])).

fof(f2212,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104 ),
    inference(resolution,[],[f2197,f729])).

fof(f729,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
        | k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35 ),
    inference(resolution,[],[f724,f225])).

fof(f724,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP3(sK6,X2,X1)
        | ~ r2_hidden(X0,X1)
        | k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f723,f118])).

fof(f723,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0)
        | ~ v1_relat_1(sK6)
        | ~ r2_hidden(X0,X1)
        | ~ sP3(sK6,X2,X1) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f715,f123])).

fof(f715,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(k2_funct_1(sK6),X0) = sK11(sK6,X0)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6)
        | ~ r2_hidden(X0,X1)
        | ~ sP3(sK6,X2,X1) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(resolution,[],[f710,f505])).

fof(f7156,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7155])).

fof(f7155,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110 ),
    inference(subsumption_resolution,[],[f2199,f2982])).

fof(f2199,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104 ),
    inference(unit_resulting_resolution,[],[f2197,f729])).

fof(f7154,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7153])).

fof(f7153,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110 ),
    inference(subsumption_resolution,[],[f2209,f2982])).

fof(f2209,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104 ),
    inference(unit_resulting_resolution,[],[f225,f2197,f724])).

fof(f7152,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | spl16_110
    | ~ spl16_111 ),
    inference(avatar_contradiction_clause,[],[f7151])).

fof(f7151,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | spl16_110
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f6779,f2982])).

fof(f6779,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(forward_demodulation,[],[f1858,f3012])).

fof(f1858,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))) = sK11(sK6,sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99 ),
    inference(resolution,[],[f1825,f710])).

fof(f7149,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | spl16_110
    | ~ spl16_111 ),
    inference(avatar_contradiction_clause,[],[f7148])).

fof(f7148,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | spl16_110
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f6793,f2982])).

fof(f6793,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(forward_demodulation,[],[f1840,f3012])).

fof(f1840,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))) = sK11(sK6,sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_99 ),
    inference(unit_resulting_resolution,[],[f1825,f710])).

fof(f7147,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | spl16_94
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(avatar_contradiction_clause,[],[f7146])).

fof(f7146,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | spl16_94
    | ~ spl16_99
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f6802,f1587])).

fof(f1587,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) != k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | spl16_94 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f1586,plain,
    ( spl16_94
  <=> sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_94])])).

fof(f7143,plain,
    ( ~ spl16_4
    | ~ spl16_90
    | spl16_94
    | ~ spl16_117 ),
    inference(avatar_contradiction_clause,[],[f7142])).

fof(f7142,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_90
    | spl16_94
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f6833,f1587])).

fof(f6833,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_90
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f1410,f4006])).

fof(f4006,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_117 ),
    inference(avatar_component_clause,[],[f4004])).

fof(f4004,plain,
    ( spl16_117
  <=> sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_117])])).

fof(f1410,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_90 ),
    inference(unit_resulting_resolution,[],[f225,f1404,f93])).

fof(f7141,plain,
    ( ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | ~ spl16_93
    | spl16_110
    | ~ spl16_117 ),
    inference(avatar_contradiction_clause,[],[f7140])).

fof(f7140,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | ~ spl16_93
    | spl16_110
    | ~ spl16_117 ),
    inference(subsumption_resolution,[],[f6836,f2982])).

fof(f6836,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | ~ spl16_93
    | ~ spl16_117 ),
    inference(forward_demodulation,[],[f1540,f4006])).

fof(f1540,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | ~ spl16_93 ),
    inference(forward_demodulation,[],[f1524,f1410])).

fof(f1524,plain,
    ( sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_35
    | ~ spl16_93 ),
    inference(unit_resulting_resolution,[],[f353,f1519,f101])).

fof(f1519,plain,
    ( r2_hidden(sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_93 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f1517,plain,
    ( spl16_93
  <=> r2_hidden(sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_93])])).

fof(f7139,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7138])).

fof(f7138,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | spl16_110 ),
    inference(subsumption_resolution,[],[f1416,f2982])).

fof(f1416,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90 ),
    inference(resolution,[],[f1404,f729])).

fof(f7137,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7136])).

fof(f7136,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | spl16_110 ),
    inference(subsumption_resolution,[],[f1406,f2982])).

fof(f1406,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90 ),
    inference(unit_resulting_resolution,[],[f1404,f729])).

fof(f7135,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7134])).

fof(f7134,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90
    | spl16_110 ),
    inference(subsumption_resolution,[],[f1415,f2982])).

fof(f1415,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_90 ),
    inference(unit_resulting_resolution,[],[f225,f1404,f724])).

fof(f7131,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_80
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7130])).

fof(f7130,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_80
    | spl16_110 ),
    inference(subsumption_resolution,[],[f1291,f2982])).

fof(f1291,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_80 ),
    inference(resolution,[],[f969,f710])).

fof(f7128,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_80
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7127])).

fof(f7127,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_80
    | spl16_110 ),
    inference(subsumption_resolution,[],[f1277,f2982])).

fof(f1277,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f969,f710])).

fof(f7126,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_80
    | spl16_94 ),
    inference(avatar_contradiction_clause,[],[f7125])).

fof(f7125,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_80
    | spl16_94 ),
    inference(subsumption_resolution,[],[f1282,f1587])).

fof(f1282,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f118,f123,f969,f108])).

fof(f7121,plain,
    ( ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7120])).

fof(f7120,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f7119,f1652])).

fof(f7119,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f7118,f2017])).

fof(f2017,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f226,f2003,f610])).

fof(f610,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP3(k2_funct_1(sK6),X2,X1)
        | ~ r2_hidden(X0,X1)
        | k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)) = X0 )
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(resolution,[],[f603,f428])).

fof(f603,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,k1_relat_1(sK6))
        | ~ r2_hidden(X1,X2)
        | ~ sP3(k2_funct_1(sK6),X0,X2) )
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f601,f414])).

fof(f601,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X1,k1_relat_1(sK6))
        | ~ r2_hidden(sK15(k2_funct_1(sK6),X0,X1),k2_relat_1(sK6))
        | ~ r2_hidden(X1,X2)
        | ~ sP3(k2_funct_1(sK6),X0,X2) )
    | ~ spl16_35 ),
    inference(superposition,[],[f593,f93])).

fof(f7118,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f5053,f4285])).

fof(f4285,plain,
    ( k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f226,f4122,f2793])).

fof(f4122,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))))
    | ~ spl16_120 ),
    inference(avatar_component_clause,[],[f4120])).

fof(f4120,plain,
    ( spl16_120
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_120])])).

fof(f5053,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f4122,f4728])).

fof(f4728,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),X0,X1)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X1,k9_relat_1(k2_funct_1(sK6),X0)) )
    | ~ spl16_8
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f4697,f159])).

fof(f4697,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),X0,X1)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X1,k9_relat_1(k2_funct_1(sK6),X0))
        | ~ sP4(k2_funct_1(sK6)) )
    | ~ spl16_38 ),
    inference(superposition,[],[f4644,f375])).

fof(f7108,plain,
    ( ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7107])).

fof(f7107,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f7106,f1652])).

fof(f7106,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f7105,f2017])).

fof(f7105,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4300,f4285])).

fof(f4300,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4281,f375])).

fof(f4281,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_8
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f226,f226,f4122,f1973])).

fof(f7097,plain,
    ( ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7096])).

fof(f7096,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f7095,f1652])).

fof(f7095,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f7094,f2017])).

fof(f7094,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f5052,f2795])).

fof(f5052,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f2003,f4728])).

fof(f7088,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7087])).

fof(f7087,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f5137,f1652])).

fof(f5137,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f5121,f375])).

fof(f5121,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f123,f118,f2003,f226,f3970])).

fof(f3970,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(k2_funct_1(X1),X3,X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(X0,k9_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1)))) ) ),
    inference(subsumption_resolution,[],[f3969,f60])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f3969,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP3(k2_funct_1(X1),X3,X2) ) ),
    inference(subsumption_resolution,[],[f3957,f61])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f3957,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(k2_funct_1(X1),k1_relat_1(k2_funct_1(X1))))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP3(k2_funct_1(X1),X3,X2) ) ),
    inference(resolution,[],[f3910,f505])).

fof(f3910,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k2_funct_1(X2)))
      | r2_hidden(X1,k9_relat_1(k2_funct_1(X2),k1_relat_1(k2_funct_1(X2))))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(subsumption_resolution,[],[f3891,f60])).

fof(f3891,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,k2_relat_1(k2_funct_1(X2)))
      | r2_hidden(X1,k9_relat_1(k2_funct_1(X2),k1_relat_1(k2_funct_1(X2))))
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f3855,f61])).

fof(f7086,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7085])).

fof(f7085,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f5136,f1652])).

fof(f5136,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f5122,f375])).

fof(f5122,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f123,f118,f4122,f226,f3970])).

fof(f7084,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7083])).

fof(f7083,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f4927,f1652])).

fof(f4927,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f4906,f375])).

fof(f4906,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f118,f123,f2003,f4858])).

fof(f4858,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X2,k9_relat_1(k2_funct_1(X3),k1_relat_1(k2_funct_1(X3))))
      | ~ r2_hidden(X2,k9_relat_1(k2_funct_1(X3),X4))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(subsumption_resolution,[],[f4837,f60])).

fof(f4837,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(X2,k9_relat_1(k2_funct_1(X3),k1_relat_1(k2_funct_1(X3))))
      | ~ r2_hidden(X2,k9_relat_1(k2_funct_1(X3),X4))
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f4782,f61])).

fof(f4782,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | r2_hidden(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ r2_hidden(X0,k9_relat_1(X1,X2))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f4754,f99])).

fof(f7082,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7081])).

fof(f7081,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f4926,f1652])).

fof(f4926,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4907,f375])).

fof(f4907,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f118,f123,f4122,f4858])).

fof(f7080,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7079])).

fof(f7079,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f4856,f1652])).

fof(f4856,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f4827,f375])).

fof(f4827,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f140,f151,f2003,f4782])).

fof(f7078,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7077])).

fof(f7077,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f4855,f1652])).

fof(f4855,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4828,f375])).

fof(f4828,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f140,f151,f4122,f4782])).

fof(f7076,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7075])).

fof(f7075,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f4806,f1652])).

fof(f4806,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f2003,f4804])).

fof(f7074,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7073])).

fof(f7073,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f4807,f1652])).

fof(f4807,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f4122,f4804])).

fof(f7072,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7071])).

fof(f7071,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f4802,f1652])).

fof(f4802,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f4773,f375])).

fof(f4773,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_8
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f159,f2003,f4754])).

fof(f7070,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7069])).

fof(f7069,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f4801,f1652])).

fof(f4801,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4774,f375])).

fof(f4774,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_8
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f159,f4122,f4754])).

fof(f7068,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7067])).

fof(f7067,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f4756,f1652])).

fof(f4756,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f4735,f375])).

fof(f4735,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_8
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f2003,f226,f159,f4727])).

fof(f7066,plain,
    ( ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7065])).

fof(f7065,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_38
    | spl16_95
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f4755,f1652])).

fof(f4755,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4736,f375])).

fof(f4736,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k1_relat_1(k2_funct_1(sK6))))
    | ~ spl16_8
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f4122,f226,f159,f4727])).

fof(f7064,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_110
    | ~ spl16_121 ),
    inference(avatar_contradiction_clause,[],[f7063])).

fof(f7063,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_110
    | ~ spl16_121 ),
    inference(subsumption_resolution,[],[f4402,f2982])).

fof(f4402,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_121 ),
    inference(resolution,[],[f4365,f729])).

fof(f4365,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))))
    | ~ spl16_121 ),
    inference(avatar_component_clause,[],[f4363])).

fof(f4363,plain,
    ( spl16_121
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_121])])).

fof(f7062,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_110
    | ~ spl16_121 ),
    inference(avatar_contradiction_clause,[],[f7061])).

fof(f7061,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_110
    | ~ spl16_121 ),
    inference(subsumption_resolution,[],[f4368,f2982])).

fof(f4368,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_121 ),
    inference(unit_resulting_resolution,[],[f4365,f729])).

fof(f7060,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_110
    | ~ spl16_121 ),
    inference(avatar_contradiction_clause,[],[f7059])).

fof(f7059,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_110
    | ~ spl16_121 ),
    inference(subsumption_resolution,[],[f4383,f2982])).

fof(f4383,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_121 ),
    inference(unit_resulting_resolution,[],[f225,f4365,f724])).

fof(f7058,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_94
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(avatar_contradiction_clause,[],[f7057])).

fof(f7057,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_94
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f7011,f1587])).

fof(f7011,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(backward_demodulation,[],[f2203,f7005])).

fof(f7056,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110
    | ~ spl16_112 ),
    inference(avatar_contradiction_clause,[],[f7055])).

fof(f7055,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f7013,f2982])).

fof(f7013,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(forward_demodulation,[],[f7006,f7005])).

fof(f7006,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(backward_demodulation,[],[f3205,f2203])).

fof(f7054,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110
    | ~ spl16_112 ),
    inference(avatar_contradiction_clause,[],[f7053])).

fof(f7053,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | spl16_110
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f7019,f2982])).

fof(f7019,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(forward_demodulation,[],[f3214,f7005])).

fof(f3214,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_104
    | ~ spl16_112 ),
    inference(forward_demodulation,[],[f3194,f2203])).

fof(f3194,plain,
    ( sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_35
    | ~ spl16_112 ),
    inference(unit_resulting_resolution,[],[f353,f3161,f101])).

fof(f7052,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_96
    | ~ spl16_105 ),
    inference(avatar_contradiction_clause,[],[f7051])).

fof(f7051,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_96
    | ~ spl16_105 ),
    inference(subsumption_resolution,[],[f2248,f1685])).

fof(f1685,plain,
    ( ~ r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | spl16_96 ),
    inference(avatar_component_clause,[],[f1684])).

fof(f1684,plain,
    ( spl16_96
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_96])])).

fof(f2248,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_105 ),
    inference(unit_resulting_resolution,[],[f140,f151,f226,f2237,f505])).

fof(f2237,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6)))))
    | ~ spl16_105 ),
    inference(avatar_component_clause,[],[f2235])).

fof(f2235,plain,
    ( spl16_105
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_105])])).

fof(f7050,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_96
    | ~ spl16_101 ),
    inference(avatar_contradiction_clause,[],[f7049])).

fof(f7049,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_96
    | ~ spl16_101 ),
    inference(subsumption_resolution,[],[f2014,f1685])).

fof(f2014,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f140,f151,f226,f2003,f505])).

fof(f7048,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_96
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7047])).

fof(f7047,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | spl16_96
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f4275,f1685])).

fof(f4275,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f151,f140,f226,f4122,f505])).

fof(f7046,plain,
    ( ~ spl16_4
    | ~ spl16_35
    | spl16_81
    | spl16_82 ),
    inference(avatar_contradiction_clause,[],[f7045])).

fof(f7045,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_35
    | spl16_81
    | spl16_82 ),
    inference(subsumption_resolution,[],[f1009,f4484])).

fof(f1009,plain,
    ( k9_relat_1(sK6,sK5) != k2_relat_1(sK6)
    | spl16_81 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f7044,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_94
    | ~ spl16_106 ),
    inference(avatar_contradiction_clause,[],[f7043])).

fof(f7043,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_94
    | ~ spl16_106 ),
    inference(subsumption_resolution,[],[f1587,f6745])).

fof(f6745,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_106 ),
    inference(backward_demodulation,[],[f2290,f2289])).

fof(f2289,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_106 ),
    inference(resolution,[],[f2274,f729])).

fof(f2274,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))))
    | ~ spl16_106 ),
    inference(avatar_component_clause,[],[f2272])).

fof(f2272,plain,
    ( spl16_106
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_106])])).

fof(f2290,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_106 ),
    inference(resolution,[],[f2274,f648])).

fof(f648,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
        | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X0)) = X0 )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35 ),
    inference(resolution,[],[f629,f225])).

fof(f629,plain,
    ( ! [X2,X0,X1] :
        ( ~ sP3(sK6,X2,X1)
        | ~ r2_hidden(X0,X1)
        | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X0)) = X0 )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f628,f118])).

fof(f628,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X0)) = X0
        | ~ v1_relat_1(sK6)
        | ~ r2_hidden(X0,X1)
        | ~ sP3(sK6,X2,X1) )
    | ~ spl16_2
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f621,f123])).

fof(f621,plain,
    ( ! [X2,X0,X1] :
        ( k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X0)) = X0
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6)
        | ~ r2_hidden(X0,X1)
        | ~ sP3(sK6,X2,X1) )
    | ~ spl16_35 ),
    inference(resolution,[],[f618,f505])).

fof(f618,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_relat_1(sK6))
        | k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X3)) = X3 )
    | ~ spl16_35 ),
    inference(resolution,[],[f104,f357])).

fof(f7042,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | spl16_95
    | ~ spl16_106 ),
    inference(avatar_contradiction_clause,[],[f7041])).

fof(f7041,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | spl16_95
    | ~ spl16_106 ),
    inference(subsumption_resolution,[],[f1652,f6759])).

fof(f6759,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_106 ),
    inference(forward_demodulation,[],[f1976,f2289])).

fof(f1976,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f969,f969,f1642])).

fof(f7040,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_96
    | ~ spl16_97
    | ~ spl16_100 ),
    inference(avatar_contradiction_clause,[],[f7039])).

fof(f7039,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | spl16_96
    | ~ spl16_97
    | ~ spl16_100 ),
    inference(subsumption_resolution,[],[f1685,f6774])).

fof(f6774,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_97
    | ~ spl16_100 ),
    inference(forward_demodulation,[],[f1756,f6764])).

fof(f6764,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_97
    | ~ spl16_100 ),
    inference(backward_demodulation,[],[f6762,f1757])).

fof(f1757,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_97 ),
    inference(unit_resulting_resolution,[],[f225,f1751,f93])).

fof(f1751,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))
    | ~ spl16_97 ),
    inference(avatar_component_clause,[],[f1749])).

fof(f1749,plain,
    ( spl16_97
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_97])])).

fof(f6762,plain,
    ( sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,k1_funct_1(sK6,sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_100 ),
    inference(forward_demodulation,[],[f1923,f1925])).

fof(f1925,plain,
    ( sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_35
    | ~ spl16_100 ),
    inference(resolution,[],[f1912,f428])).

fof(f1912,plain,
    ( r2_hidden(sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_100 ),
    inference(avatar_component_clause,[],[f1910])).

fof(f1910,plain,
    ( spl16_100
  <=> r2_hidden(sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_100])])).

fof(f1923,plain,
    ( k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))) = sK11(sK6,k1_funct_1(sK6,sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_100 ),
    inference(resolution,[],[f1912,f726])).

fof(f1756,plain,
    ( r2_hidden(sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_4
    | ~ spl16_97 ),
    inference(unit_resulting_resolution,[],[f225,f1751,f92])).

fof(f7038,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_98
    | ~ spl16_106
    | ~ spl16_120 ),
    inference(avatar_contradiction_clause,[],[f7037])).

fof(f7037,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | spl16_98
    | ~ spl16_106
    | ~ spl16_120 ),
    inference(subsumption_resolution,[],[f1774,f6921])).

fof(f6921,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_106
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4270,f6912])).

fof(f6912,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_106
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4290,f6745])).

fof(f4290,plain,
    ( k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_120 ),
    inference(resolution,[],[f4122,f2796])).

fof(f4270,plain,
    ( r2_hidden(sK15(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))
    | ~ spl16_8
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f226,f4122,f92])).

fof(f1774,plain,
    ( ~ r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))
    | spl16_98 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f1773,plain,
    ( spl16_98
  <=> r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_98])])).

fof(f7036,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_101
    | spl16_102
    | ~ spl16_106 ),
    inference(avatar_contradiction_clause,[],[f7035])).

fof(f7035,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_101
    | spl16_102
    | ~ spl16_106 ),
    inference(subsumption_resolution,[],[f7034,f969])).

fof(f7034,plain,
    ( ~ r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | spl16_102
    | ~ spl16_106 ),
    inference(forward_demodulation,[],[f2039,f6747])).

fof(f6747,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | ~ spl16_106 ),
    inference(backward_demodulation,[],[f4862,f6745])).

fof(f7033,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_106
    | spl16_110 ),
    inference(avatar_contradiction_clause,[],[f7032])).

fof(f7032,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_106
    | spl16_110 ),
    inference(subsumption_resolution,[],[f2982,f2289])).

fof(f7031,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | ~ spl16_106
    | spl16_126 ),
    inference(avatar_contradiction_clause,[],[f7030])).

fof(f7030,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_101
    | ~ spl16_106
    | spl16_126 ),
    inference(subsumption_resolution,[],[f5621,f6747])).

fof(f5621,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) != sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | spl16_126 ),
    inference(avatar_component_clause,[],[f5620])).

fof(f5620,plain,
    ( spl16_126
  <=> sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_126])])).

fof(f6722,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(avatar_contradiction_clause,[],[f6721])).

fof(f6721,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6720,f118])).

fof(f6720,plain,
    ( ~ v1_relat_1(sK6)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6719,f123])).

fof(f6719,plain,
    ( ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6718,f299])).

fof(f6718,plain,
    ( sP3(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6717,f6389])).

fof(f6717,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | sP3(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6659,f6671])).

fof(f6671,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(backward_demodulation,[],[f6555,f6636])).

fof(f6636,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))) = sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_136 ),
    inference(unit_resulting_resolution,[],[f964,f6586,f724])).

fof(f964,plain,
    ( sP3(sK6,sK5,k2_relat_1(sK6))
    | ~ spl16_79 ),
    inference(avatar_component_clause,[],[f963])).

fof(f6555,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_133 ),
    inference(unit_resulting_resolution,[],[f140,f151,f6389,f111])).

fof(f6659,plain,
    ( ~ r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | sP3(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6)
    | ~ spl16_136 ),
    inference(resolution,[],[f6586,f2740])).

fof(f6716,plain,
    ( ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(avatar_contradiction_clause,[],[f6715])).

fof(f6715,plain,
    ( $false
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6588,f6671])).

fof(f6588,plain,
    ( ~ r2_hidden(sK11(sK6,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | spl16_29
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(unit_resulting_resolution,[],[f118,f123,f299,f6389,f6586,f2740])).

fof(f6714,plain,
    ( spl16_29
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(avatar_contradiction_clause,[],[f6713])).

fof(f6713,plain,
    ( $false
    | spl16_29
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(subsumption_resolution,[],[f6589,f6629])).

fof(f6629,plain,
    ( r2_hidden(sK15(sK6,sK5,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_79
    | ~ spl16_136 ),
    inference(unit_resulting_resolution,[],[f964,f6586,f92])).

fof(f6589,plain,
    ( ~ r2_hidden(sK15(sK6,sK5,sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | spl16_29
    | ~ spl16_79
    | ~ spl16_133
    | ~ spl16_136 ),
    inference(unit_resulting_resolution,[],[f964,f299,f6389,f6586,f2686])).

fof(f6587,plain,
    ( spl16_136
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_133 ),
    inference(avatar_split_clause,[],[f6560,f6387,f373,f149,f138,f6584])).

fof(f6560,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_133 ),
    inference(forward_demodulation,[],[f6556,f375])).

fof(f6556,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_133 ),
    inference(unit_resulting_resolution,[],[f140,f151,f6389,f112])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | r2_hidden(X4,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6478,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(avatar_contradiction_clause,[],[f6477])).

fof(f6477,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(subsumption_resolution,[],[f6476,f6468])).

fof(f6468,plain,
    ( r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | spl16_29
    | ~ spl16_79
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(forward_demodulation,[],[f6453,f6403])).

fof(f6403,plain,
    ( sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(sK6,sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))
    | spl16_29
    | spl16_133 ),
    inference(unit_resulting_resolution,[],[f299,f6388,f97])).

fof(f6453,plain,
    ( r2_hidden(k1_funct_1(sK6,sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),k2_relat_1(sK6))
    | ~ spl16_79
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(unit_resulting_resolution,[],[f964,f6393,f6416,f114])).

fof(f6476,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_38
    | spl16_133
    | ~ spl16_134
    | ~ spl16_135 ),
    inference(subsumption_resolution,[],[f6475,f6393])).

fof(f6475,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_35
    | ~ spl16_38
    | spl16_133
    | ~ spl16_135 ),
    inference(backward_demodulation,[],[f6409,f6474])).

fof(f6474,plain,
    ( sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)))
    | spl16_29
    | ~ spl16_35
    | spl16_133
    | ~ spl16_135 ),
    inference(forward_demodulation,[],[f6448,f6403])).

fof(f6448,plain,
    ( sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))))
    | ~ spl16_35
    | ~ spl16_135 ),
    inference(unit_resulting_resolution,[],[f353,f6416,f101])).

fof(f6409,plain,
    ( ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k2_relat_1(sK6))
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_133 ),
    inference(forward_demodulation,[],[f6408,f375])).

fof(f6408,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_133 ),
    inference(subsumption_resolution,[],[f6407,f140])).

fof(f6407,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_7
    | spl16_133 ),
    inference(subsumption_resolution,[],[f6405,f151])).

fof(f6405,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))),sK5)
    | ~ r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl16_133 ),
    inference(resolution,[],[f6388,f110])).

fof(f6417,plain,
    ( spl16_135
    | spl16_29
    | spl16_133 ),
    inference(avatar_split_clause,[],[f6401,f6387,f297,f6414])).

fof(f6401,plain,
    ( r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k1_relat_1(sK6))
    | spl16_29
    | spl16_133 ),
    inference(unit_resulting_resolution,[],[f299,f6388,f95])).

fof(f6394,plain,
    ( spl16_133
    | spl16_134
    | spl16_29 ),
    inference(avatar_split_clause,[],[f541,f297,f6391,f6387])).

fof(f541,plain,
    ( r2_hidden(sK14(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),sK5)
    | r2_hidden(sK13(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5)),k10_relat_1(k2_funct_1(sK6),sK5))
    | spl16_29 ),
    inference(resolution,[],[f96,f299])).

fof(f6381,plain,
    ( spl16_132
    | ~ spl16_129
    | ~ spl16_130 ),
    inference(avatar_split_clause,[],[f6365,f6338,f6333,f6378])).

fof(f6378,plain,
    ( spl16_132
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_132])])).

fof(f6333,plain,
    ( spl16_129
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_129])])).

fof(f6338,plain,
    ( spl16_130
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_130])])).

fof(f6365,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))))
    | ~ spl16_129
    | ~ spl16_130 ),
    inference(unit_resulting_resolution,[],[f6335,f6340,f99])).

fof(f6340,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))))
    | ~ spl16_130 ),
    inference(avatar_component_clause,[],[f6338])).

fof(f6335,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))))
    | ~ spl16_129 ),
    inference(avatar_component_clause,[],[f6333])).

fof(f6361,plain,
    ( spl16_131
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(avatar_split_clause,[],[f4554,f4541,f4536,f126,f121,f116,f6358])).

fof(f6358,plain,
    ( spl16_131
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_131])])).

fof(f126,plain,
    ( spl16_3
  <=> v2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f4536,plain,
    ( spl16_122
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_122])])).

fof(f4541,plain,
    ( spl16_123
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_123])])).

fof(f4554,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(unit_resulting_resolution,[],[f4538,f4543,f335])).

fof(f335,plain,
    ( ! [X0] :
        ( sP2(sK6,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0) )
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3 ),
    inference(subsumption_resolution,[],[f334,f118])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sP2(sK6,X0)
        | ~ v1_relat_1(sK6) )
    | ~ spl16_2
    | ~ spl16_3 ),
    inference(subsumption_resolution,[],[f333,f123])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | sP2(sK6,X0)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl16_3 ),
    inference(resolution,[],[f76,f128])).

fof(f128,plain,
    ( v2_funct_1(sK6)
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | sP2(X0,X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f13,f22,f21,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k2_funct_1(X0) = X1
      <=> sP1(X1,X0) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_funct_1(X0) = X1
          <=> ( ! [X2,X3] :
                  ( ( ( k1_funct_1(X1,X2) = X3
                      & r2_hidden(X2,k2_relat_1(X0)) )
                    | k1_funct_1(X0,X3) != X2
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  & ( ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                    | k1_funct_1(X1,X2) != X3
                    | ~ r2_hidden(X2,k2_relat_1(X0)) ) )
              & k2_relat_1(X0) = k1_relat_1(X1) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( k2_funct_1(X0) = X1
            <=> ( ! [X2,X3] :
                    ( ( ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) )
                     => ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) ) )
                    & ( ( k1_funct_1(X1,X2) = X3
                        & r2_hidden(X2,k2_relat_1(X0)) )
                     => ( k1_funct_1(X0,X3) = X2
                        & r2_hidden(X3,k1_relat_1(X0)) ) ) )
                & k2_relat_1(X0) = k1_relat_1(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_funct_1)).

fof(f4543,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))
    | ~ spl16_123 ),
    inference(avatar_component_clause,[],[f4541])).

fof(f4538,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))
    | ~ spl16_122 ),
    inference(avatar_component_clause,[],[f4536])).

fof(f6341,plain,
    ( spl16_130
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(avatar_split_clause,[],[f4551,f4541,f4536,f6338])).

fof(f4551,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))))
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(unit_resulting_resolution,[],[f4538,f4543,f61])).

fof(f6336,plain,
    ( spl16_129
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(avatar_split_clause,[],[f4550,f4541,f4536,f6333])).

fof(f4550,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))))
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(unit_resulting_resolution,[],[f4538,f4543,f60])).

fof(f6003,plain,
    ( ~ spl16_8
    | ~ spl16_127 ),
    inference(avatar_contradiction_clause,[],[f6002])).

fof(f6002,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_127 ),
    inference(subsumption_resolution,[],[f5993,f159])).

fof(f5993,plain,
    ( ~ sP4(k2_funct_1(sK6))
    | ~ spl16_127 ),
    inference(resolution,[],[f5962,f113])).

fof(f5962,plain,
    ( ! [X14] : ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X14)
    | ~ spl16_127 ),
    inference(avatar_component_clause,[],[f5961])).

fof(f5961,plain,
    ( spl16_127
  <=> ! [X14] : ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_127])])).

fof(f6001,plain,
    ( ~ spl16_8
    | ~ spl16_127 ),
    inference(avatar_contradiction_clause,[],[f6000])).

fof(f6000,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_127 ),
    inference(subsumption_resolution,[],[f5990,f159])).

fof(f5990,plain,
    ( ~ sP4(k2_funct_1(sK6))
    | ~ spl16_127 ),
    inference(unit_resulting_resolution,[],[f5962,f113])).

fof(f5999,plain,
    ( ~ spl16_8
    | ~ spl16_127 ),
    inference(avatar_contradiction_clause,[],[f5991])).

fof(f5991,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_127 ),
    inference(unit_resulting_resolution,[],[f159,f5962,f113])).

fof(f5998,plain,
    ( ~ spl16_8
    | ~ spl16_127 ),
    inference(avatar_contradiction_clause,[],[f5989])).

fof(f5989,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_127 ),
    inference(unit_resulting_resolution,[],[f226,f5962])).

fof(f5997,plain,
    ( ~ spl16_8
    | ~ spl16_127 ),
    inference(avatar_contradiction_clause,[],[f5992])).

fof(f5992,plain,
    ( $false
    | ~ spl16_8
    | ~ spl16_127 ),
    inference(resolution,[],[f5962,f226])).

fof(f5966,plain,
    ( spl16_127
    | spl16_128
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_108 ),
    inference(avatar_split_clause,[],[f5936,f2460,f963,f373,f351,f157,f149,f138,f5964,f5961])).

fof(f5964,plain,
    ( spl16_128
  <=> ! [X13] :
        ( r2_hidden(k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X13)),k2_relat_1(sK6))
        | ~ r2_hidden(X13,k2_relat_1(sK6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_128])])).

fof(f5936,plain,
    ( ! [X14,X13] :
        ( r2_hidden(k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X13)),k2_relat_1(sK6))
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X14)
        | ~ r2_hidden(X13,k2_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_108 ),
    inference(forward_demodulation,[],[f5935,f375])).

fof(f5935,plain,
    ( ! [X14,X13] :
        ( r2_hidden(k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X13)),k1_relat_1(k2_funct_1(sK6)))
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X14)
        | ~ r2_hidden(X13,k2_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_108 ),
    inference(subsumption_resolution,[],[f5907,f558])).

fof(f5907,plain,
    ( ! [X14,X13] :
        ( r2_hidden(k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X13)),k1_relat_1(k2_funct_1(sK6)))
        | ~ r2_hidden(k1_funct_1(k2_funct_1(sK6),X13),X14)
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X14)
        | ~ r2_hidden(X13,k2_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_108 ),
    inference(superposition,[],[f91,f3700])).

fof(f3700,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),X0)) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),k1_funct_1(k2_funct_1(sK6),X0))
        | ~ r2_hidden(X0,k2_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_108 ),
    inference(resolution,[],[f3661,f2796])).

fof(f3661,plain,
    ( ! [X13] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),X13),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X13,k2_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_108 ),
    inference(resolution,[],[f3651,f964])).

fof(f3651,plain,
    ( ! [X6,X7,X5] :
        ( ~ sP3(sK6,X5,X7)
        | ~ r2_hidden(X6,X7)
        | r2_hidden(k1_funct_1(k2_funct_1(sK6),X6),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(subsumption_resolution,[],[f3640,f91])).

fof(f3640,plain,
    ( ! [X6,X7,X5] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),X6),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(sK15(sK6,X5,X6),k1_relat_1(sK6))
        | ~ r2_hidden(X6,X7)
        | ~ sP3(sK6,X5,X7) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(superposition,[],[f3553,f93])).

fof(f3553,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(duplicate_literal_removal,[],[f3550])).

fof(f3550,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,X0)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(superposition,[],[f3539,f2547])).

fof(f2547,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) = sK11(k2_funct_1(sK6),X0)
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(backward_demodulation,[],[f2369,f2462])).

fof(f2462,plain,
    ( k1_relat_1(sK6) = k2_relat_1(k2_funct_1(sK6))
    | ~ spl16_108 ),
    inference(avatar_component_clause,[],[f2460])).

fof(f2369,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) = sK11(k2_funct_1(sK6),X0)
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f2368,f140])).

fof(f2368,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) = sK11(k2_funct_1(sK6),X0)
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f2367,f151])).

fof(f2367,plain,
    ( ! [X0] :
        ( k1_funct_1(sK6,X0) = sK11(k2_funct_1(sK6),X0)
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f2366,f357])).

fof(f2366,plain,
    ( ! [X0] :
        ( ~ sP0(sK11(k2_funct_1(sK6),X0),X0,sK6,k2_funct_1(sK6))
        | k1_funct_1(sK6,X0) = sK11(k2_funct_1(sK6),X0)
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(duplicate_literal_removal,[],[f2361])).

fof(f2361,plain,
    ( ! [X0] :
        ( ~ sP0(sK11(k2_funct_1(sK6),X0),X0,sK6,k2_funct_1(sK6))
        | k1_funct_1(sK6,X0) = sK11(k2_funct_1(sK6),X0)
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6))
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(resolution,[],[f620,f465])).

fof(f620,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(sK11(X5,X6),k2_relat_1(X7))
      | ~ sP0(sK11(X5,X6),X6,X7,X5)
      | sK11(X5,X6) = k1_funct_1(X7,X6)
      | ~ r2_hidden(X6,k2_relat_1(X5))
      | ~ v1_funct_1(X5)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f104,f108])).

fof(f3539,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),X0)),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
        | ~ r2_hidden(X0,k1_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(resolution,[],[f2511,f226])).

fof(f2511,plain,
    ( ! [X4,X5] :
        ( ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X5)
        | r2_hidden(k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),X4)),X5)
        | ~ r2_hidden(X4,k1_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(backward_demodulation,[],[f1623,f2462])).

fof(f1623,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),X4)),X5)
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X5)
        | ~ r2_hidden(X4,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f1622,f140])).

fof(f1622,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),X4)),X5)
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X5)
        | ~ r2_hidden(X4,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f1616,f151])).

fof(f1616,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),X4)),X5)
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X5)
        | ~ r2_hidden(X4,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(duplicate_literal_removal,[],[f1608])).

fof(f1608,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),X4)),X5)
        | ~ sP3(k2_funct_1(sK6),k2_relat_1(sK6),X5)
        | ~ r2_hidden(X4,k2_relat_1(k2_funct_1(sK6)))
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6))
        | ~ r2_hidden(X4,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(resolution,[],[f555,f465])).

fof(f5623,plain,
    ( spl16_126
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_94
    | ~ spl16_95
    | ~ spl16_102 ),
    inference(avatar_split_clause,[],[f2091,f2038,f1651,f1586,f963,f351,f157,f121,f116,f5620])).

fof(f2091,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_94
    | ~ spl16_95
    | ~ spl16_102 ),
    inference(forward_demodulation,[],[f2090,f1588])).

fof(f1588,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_94 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f2090,plain,
    ( k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_95
    | ~ spl16_102 ),
    inference(forward_demodulation,[],[f2081,f1660])).

fof(f1660,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_8
    | ~ spl16_95 ),
    inference(unit_resulting_resolution,[],[f226,f1653,f93])).

fof(f1653,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_95 ),
    inference(avatar_component_clause,[],[f1651])).

fof(f2081,plain,
    ( sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_102 ),
    inference(unit_resulting_resolution,[],[f964,f2040,f629])).

fof(f2040,plain,
    ( r2_hidden(sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_102 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f4567,plain,
    ( spl16_125
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(avatar_split_clause,[],[f4553,f4541,f4536,f4564])).

fof(f4564,plain,
    ( spl16_125
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_125])])).

fof(f4553,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))
    | ~ spl16_122
    | ~ spl16_123 ),
    inference(unit_resulting_resolution,[],[f4538,f4543,f99])).

fof(f4549,plain,
    ( spl16_124
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(avatar_split_clause,[],[f3286,f3273,f3268,f126,f121,f116,f4546])).

fof(f4546,plain,
    ( spl16_124
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_124])])).

fof(f3268,plain,
    ( spl16_113
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_113])])).

fof(f3273,plain,
    ( spl16_114
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_114])])).

fof(f3286,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(unit_resulting_resolution,[],[f3270,f3275,f335])).

fof(f3275,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))
    | ~ spl16_114 ),
    inference(avatar_component_clause,[],[f3273])).

fof(f3270,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))
    | ~ spl16_113 ),
    inference(avatar_component_clause,[],[f3268])).

fof(f4544,plain,
    ( spl16_123
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(avatar_split_clause,[],[f3283,f3273,f3268,f4541])).

fof(f3283,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(unit_resulting_resolution,[],[f3270,f3275,f61])).

fof(f4539,plain,
    ( spl16_122
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(avatar_split_clause,[],[f3282,f3273,f3268,f4536])).

fof(f3282,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))))
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(unit_resulting_resolution,[],[f3270,f3275,f60])).

fof(f4366,plain,
    ( spl16_121
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_85
    | ~ spl16_94
    | ~ spl16_108
    | ~ spl16_120 ),
    inference(avatar_split_clause,[],[f4297,f4120,f2460,f1586,f1111,f373,f351,f149,f138,f133,f4363])).

fof(f1111,plain,
    ( spl16_85
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_85])])).

fof(f4297,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_85
    | ~ spl16_94
    | ~ spl16_108
    | ~ spl16_120 ),
    inference(forward_demodulation,[],[f4283,f1588])).

fof(f4283,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_85
    | ~ spl16_108
    | ~ spl16_120 ),
    inference(unit_resulting_resolution,[],[f1113,f4122,f2488])).

fof(f2488,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1))
        | ~ r2_hidden(X0,k1_relat_1(sK6))
        | ~ r2_hidden(X0,X1) )
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_108 ),
    inference(backward_demodulation,[],[f872,f2462])).

fof(f872,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k1_funct_1(sK6,X0),k9_relat_1(sK6,X1))
        | ~ r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(resolution,[],[f608,f225])).

fof(f608,plain,
    ( ! [X2,X3,X1] :
        ( ~ sP3(sK6,X2,X3)
        | ~ r2_hidden(X1,X2)
        | r2_hidden(k1_funct_1(sK6,X1),X3)
        | ~ r2_hidden(X1,k2_relat_1(k2_funct_1(sK6))) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(resolution,[],[f606,f114])).

fof(f1113,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_85 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f4123,plain,
    ( spl16_120
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_98 ),
    inference(avatar_split_clause,[],[f1792,f1773,f967,f963,f373,f351,f157,f121,f116,f4120])).

fof(f1792,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_98 ),
    inference(forward_demodulation,[],[f1785,f1290])).

fof(f1290,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f964,f969,f724])).

fof(f1785,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_98 ),
    inference(unit_resulting_resolution,[],[f969,f226,f1775,f558])).

fof(f1775,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))
    | ~ spl16_98 ),
    inference(avatar_component_clause,[],[f1773])).

fof(f4099,plain,
    ( spl16_118
    | ~ spl16_119
    | ~ spl16_43 ),
    inference(avatar_split_clause,[],[f421,f417,f4096,f4092])).

fof(f4092,plain,
    ( spl16_118
  <=> k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_118])])).

fof(f4096,plain,
    ( spl16_119
  <=> sP1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_119])])).

fof(f417,plain,
    ( spl16_43
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_43])])).

fof(f421,plain,
    ( ~ sP1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))),sK6)
    | k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_43 ),
    inference(resolution,[],[f419,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ sP1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( k2_funct_1(X0) = X1
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | k2_funct_1(X0) != X1 ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f419,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_43 ),
    inference(avatar_component_clause,[],[f417])).

fof(f4007,plain,
    ( spl16_117
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_90
    | ~ spl16_93 ),
    inference(avatar_split_clause,[],[f1541,f1517,f1402,f967,f963,f351,f133,f121,f116,f4004])).

fof(f1541,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_90
    | ~ spl16_93 ),
    inference(forward_demodulation,[],[f1540,f1290])).

fof(f3306,plain,
    ( spl16_116
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(avatar_split_clause,[],[f3285,f3273,f3268,f3303])).

fof(f3303,plain,
    ( spl16_116
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_116])])).

fof(f3285,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))
    | ~ spl16_113
    | ~ spl16_114 ),
    inference(unit_resulting_resolution,[],[f3270,f3275,f99])).

fof(f3281,plain,
    ( spl16_115
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(avatar_split_clause,[],[f937,f924,f919,f126,f121,f116,f3278])).

fof(f3278,plain,
    ( spl16_115
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_115])])).

fof(f919,plain,
    ( spl16_75
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_75])])).

fof(f924,plain,
    ( spl16_76
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_76])])).

fof(f937,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(unit_resulting_resolution,[],[f921,f926,f335])).

fof(f926,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))
    | ~ spl16_76 ),
    inference(avatar_component_clause,[],[f924])).

fof(f921,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))
    | ~ spl16_75 ),
    inference(avatar_component_clause,[],[f919])).

fof(f3276,plain,
    ( spl16_114
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(avatar_split_clause,[],[f934,f924,f919,f3273])).

fof(f934,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(unit_resulting_resolution,[],[f921,f926,f61])).

fof(f3271,plain,
    ( spl16_113
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(avatar_split_clause,[],[f933,f924,f919,f3268])).

fof(f933,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))))
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(unit_resulting_resolution,[],[f921,f926,f60])).

fof(f3162,plain,
    ( spl16_112
    | ~ spl16_4
    | ~ spl16_104 ),
    inference(avatar_split_clause,[],[f2201,f2195,f133,f3159])).

fof(f2201,plain,
    ( r2_hidden(sK15(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_4
    | ~ spl16_104 ),
    inference(unit_resulting_resolution,[],[f225,f2197,f91])).

fof(f3013,plain,
    ( spl16_111
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_94
    | ~ spl16_96
    | ~ spl16_99 ),
    inference(avatar_split_clause,[],[f1862,f1823,f1684,f1586,f963,f351,f149,f138,f121,f116,f3010])).

fof(f1862,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_94
    | ~ spl16_96
    | ~ spl16_99 ),
    inference(forward_demodulation,[],[f1861,f1588])).

fof(f1861,plain,
    ( k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_96
    | ~ spl16_99 ),
    inference(forward_demodulation,[],[f1854,f1708])).

fof(f1708,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_96 ),
    inference(unit_resulting_resolution,[],[f140,f151,f1686,f108])).

fof(f1686,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_96 ),
    inference(avatar_component_clause,[],[f1684])).

fof(f1854,plain,
    ( sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))) = k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_99 ),
    inference(unit_resulting_resolution,[],[f964,f1825,f629])).

fof(f2984,plain,
    ( spl16_110
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(avatar_split_clause,[],[f1290,f967,f963,f351,f121,f116,f2981])).

fof(f2467,plain,
    ( spl16_108
    | spl16_109
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(avatar_split_clause,[],[f2454,f373,f351,f149,f138,f2464,f2460])).

fof(f2454,plain,
    ( r2_hidden(sK9(k2_funct_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6))
    | k1_relat_1(sK6) = k2_relat_1(k2_funct_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(factoring,[],[f746])).

fof(f746,plain,
    ( ! [X11] :
        ( r2_hidden(sK9(k2_funct_1(sK6),X11),k1_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X11
        | r2_hidden(sK9(k2_funct_1(sK6),X11),X11) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f745,f684])).

fof(f684,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(k2_funct_1(sK6),X0),k2_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X0
        | r2_hidden(sK9(k2_funct_1(sK6),X0),X0) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f683,f140])).

fof(f683,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(k2_funct_1(sK6),X0),k2_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X0
        | r2_hidden(sK9(k2_funct_1(sK6),X0),X0)
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(subsumption_resolution,[],[f680,f151])).

fof(f680,plain,
    ( ! [X0] :
        ( r2_hidden(sK10(k2_funct_1(sK6),X0),k2_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X0
        | r2_hidden(sK9(k2_funct_1(sK6),X0),X0)
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_38 ),
    inference(superposition,[],[f80,f375])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK10(X0,X1),k1_relat_1(X0))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK9(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f745,plain,
    ( ! [X11] :
        ( r2_hidden(sK9(k2_funct_1(sK6),X11),k1_relat_1(sK6))
        | ~ r2_hidden(sK10(k2_funct_1(sK6),X11),k2_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X11
        | r2_hidden(sK9(k2_funct_1(sK6),X11),X11) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f744,f140])).

fof(f744,plain,
    ( ! [X11] :
        ( r2_hidden(sK9(k2_funct_1(sK6),X11),k1_relat_1(sK6))
        | ~ r2_hidden(sK10(k2_funct_1(sK6),X11),k2_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X11
        | r2_hidden(sK9(k2_funct_1(sK6),X11),X11)
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_7
    | ~ spl16_35 ),
    inference(subsumption_resolution,[],[f738,f151])).

fof(f738,plain,
    ( ! [X11] :
        ( r2_hidden(sK9(k2_funct_1(sK6),X11),k1_relat_1(sK6))
        | ~ r2_hidden(sK10(k2_funct_1(sK6),X11),k2_relat_1(sK6))
        | k2_relat_1(k2_funct_1(sK6)) = X11
        | r2_hidden(sK9(k2_funct_1(sK6),X11),X11)
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_35 ),
    inference(superposition,[],[f593,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( sK9(X0,X1) = k1_funct_1(X0,sK10(X0,X1))
      | k2_relat_1(X0) = X1
      | r2_hidden(sK9(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2320,plain,
    ( spl16_107
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_91 ),
    inference(avatar_split_clause,[],[f1468,f1423,f967,f963,f351,f121,f116,f2317])).

fof(f2317,plain,
    ( spl16_107
  <=> sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_107])])).

fof(f1423,plain,
    ( spl16_91
  <=> r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_91])])).

fof(f1468,plain,
    ( sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_91 ),
    inference(forward_demodulation,[],[f1467,f1290])).

fof(f1467,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_91 ),
    inference(forward_demodulation,[],[f1446,f1286])).

fof(f1286,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f964,f969,f93])).

fof(f1446,plain,
    ( sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))) = k1_funct_1(k2_funct_1(sK6),k1_funct_1(sK6,sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))))
    | ~ spl16_35
    | ~ spl16_91 ),
    inference(unit_resulting_resolution,[],[f353,f1425,f101])).

fof(f1425,plain,
    ( r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_91 ),
    inference(avatar_component_clause,[],[f1423])).

fof(f2275,plain,
    ( spl16_106
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_94
    | ~ spl16_96
    | ~ spl16_105 ),
    inference(avatar_split_clause,[],[f2257,f2235,f1684,f1586,f373,f351,f149,f138,f133,f2272])).

fof(f2257,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_94
    | ~ spl16_96
    | ~ spl16_105 ),
    inference(forward_demodulation,[],[f2253,f1588])).

fof(f2253,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_96
    | ~ spl16_105 ),
    inference(unit_resulting_resolution,[],[f1686,f2237,f872])).

fof(f2238,plain,
    ( spl16_105
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_97 ),
    inference(avatar_split_clause,[],[f1768,f1749,f967,f963,f373,f351,f157,f121,f116,f2235])).

fof(f1768,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_97 ),
    inference(forward_demodulation,[],[f1761,f1290])).

fof(f1761,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6)))))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_80
    | ~ spl16_97 ),
    inference(unit_resulting_resolution,[],[f226,f969,f1751,f558])).

fof(f2198,plain,
    ( spl16_104
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_94
    | ~ spl16_96
    | ~ spl16_101 ),
    inference(avatar_split_clause,[],[f2023,f2001,f1684,f1586,f373,f351,f149,f138,f133,f2195])).

fof(f2023,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_94
    | ~ spl16_96
    | ~ spl16_101 ),
    inference(forward_demodulation,[],[f2019,f1588])).

fof(f2019,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6)))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_96
    | ~ spl16_101 ),
    inference(unit_resulting_resolution,[],[f1686,f2003,f872])).

fof(f2145,plain,
    ( spl16_103
    | ~ spl16_4
    | ~ spl16_98 ),
    inference(avatar_split_clause,[],[f1779,f1773,f133,f2142])).

fof(f2142,plain,
    ( spl16_103
  <=> r2_hidden(sK15(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_103])])).

fof(f1779,plain,
    ( r2_hidden(sK15(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_4
    | ~ spl16_98 ),
    inference(unit_resulting_resolution,[],[f225,f1775,f91])).

fof(f2041,plain,
    ( spl16_102
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_95 ),
    inference(avatar_split_clause,[],[f1663,f1651,f373,f157,f2038])).

fof(f1663,plain,
    ( r2_hidden(sK15(k2_funct_1(sK6),k2_relat_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_8
    | ~ spl16_38
    | ~ spl16_95 ),
    inference(unit_resulting_resolution,[],[f226,f1653,f414])).

fof(f2004,plain,
    ( spl16_101
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_90 ),
    inference(avatar_split_clause,[],[f1647,f1402,f967,f963,f373,f351,f157,f121,f116,f2001])).

fof(f1647,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k9_relat_1(sK6,k1_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_90 ),
    inference(forward_demodulation,[],[f1641,f1290])).

fof(f1913,plain,
    ( spl16_100
    | ~ spl16_4
    | ~ spl16_97 ),
    inference(avatar_split_clause,[],[f1755,f1749,f133,f1910])).

fof(f1755,plain,
    ( r2_hidden(sK15(sK6,k2_relat_1(k2_funct_1(sK6)),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_4
    | ~ spl16_97 ),
    inference(unit_resulting_resolution,[],[f225,f1751,f91])).

fof(f1826,plain,
    ( spl16_99
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_96 ),
    inference(avatar_split_clause,[],[f1720,f1684,f373,f149,f138,f1823])).

fof(f1720,plain,
    ( r2_hidden(sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | ~ spl16_96 ),
    inference(forward_demodulation,[],[f1709,f375])).

fof(f1709,plain,
    ( r2_hidden(sK11(k2_funct_1(sK6),sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_96 ),
    inference(unit_resulting_resolution,[],[f140,f151,f1686,f109])).

fof(f1776,plain,
    ( spl16_98
    | ~ spl16_4
    | ~ spl16_85
    | ~ spl16_94
    | ~ spl16_95 ),
    inference(avatar_split_clause,[],[f1673,f1651,f1586,f1111,f133,f1773])).

fof(f1673,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_85
    | ~ spl16_94
    | ~ spl16_95 ),
    inference(forward_demodulation,[],[f1661,f1588])).

fof(f1661,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6))))
    | ~ spl16_4
    | ~ spl16_85
    | ~ spl16_95 ),
    inference(unit_resulting_resolution,[],[f225,f1113,f1653,f114])).

fof(f1752,plain,
    ( spl16_97
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_94
    | ~ spl16_96 ),
    inference(avatar_split_clause,[],[f1717,f1684,f1586,f373,f351,f149,f138,f133,f1749])).

fof(f1717,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_94
    | ~ spl16_96 ),
    inference(forward_demodulation,[],[f1712,f1588])).

fof(f1712,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k2_relat_1(k2_funct_1(sK6))))
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_96 ),
    inference(unit_resulting_resolution,[],[f1686,f1686,f872])).

fof(f1687,plain,
    ( spl16_96
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_95 ),
    inference(avatar_split_clause,[],[f1664,f1651,f157,f149,f138,f1684])).

fof(f1664,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_8
    | ~ spl16_95 ),
    inference(unit_resulting_resolution,[],[f140,f151,f226,f1653,f505])).

fof(f1654,plain,
    ( spl16_95
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(avatar_split_clause,[],[f1648,f967,f963,f373,f351,f157,f121,f116,f1651])).

fof(f1648,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k9_relat_1(k2_funct_1(sK6),k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_8
    | ~ spl16_35
    | ~ spl16_38
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(forward_demodulation,[],[f1640,f1290])).

fof(f1589,plain,
    ( spl16_94
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(avatar_split_clause,[],[f1293,f967,f963,f351,f121,f116,f1586])).

fof(f1293,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(forward_demodulation,[],[f1289,f1290])).

fof(f1289,plain,
    ( sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)) = k1_funct_1(sK6,k1_funct_1(k2_funct_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f964,f969,f629])).

fof(f1520,plain,
    ( spl16_93
    | ~ spl16_4
    | ~ spl16_90 ),
    inference(avatar_split_clause,[],[f1409,f1402,f133,f1517])).

fof(f1409,plain,
    ( r2_hidden(sK15(sK6,k1_relat_1(sK6),sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_4
    | ~ spl16_90 ),
    inference(unit_resulting_resolution,[],[f225,f1404,f92])).

fof(f1496,plain,
    ( spl16_92
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_89
    | ~ spl16_91 ),
    inference(avatar_split_clause,[],[f1470,f1423,f1377,f967,f963,f351,f121,f116,f1493])).

fof(f1493,plain,
    ( spl16_92
  <=> r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_92])])).

fof(f1470,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_89
    | ~ spl16_91 ),
    inference(backward_demodulation,[],[f1379,f1468])).

fof(f1379,plain,
    ( r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),sK5)
    | ~ spl16_89 ),
    inference(avatar_component_clause,[],[f1377])).

fof(f1426,plain,
    ( spl16_91
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(avatar_split_clause,[],[f1284,f967,f963,f1423])).

fof(f1284,plain,
    ( r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f964,f969,f91])).

fof(f1405,plain,
    ( spl16_90
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_85 ),
    inference(avatar_split_clause,[],[f1360,f1111,f967,f963,f351,f133,f121,f116,f1402])).

fof(f1360,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_4
    | ~ spl16_35
    | ~ spl16_79
    | ~ spl16_80
    | ~ spl16_85 ),
    inference(forward_demodulation,[],[f1354,f1293])).

fof(f1354,plain,
    ( r2_hidden(k1_funct_1(sK6,sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)))),k9_relat_1(sK6,k1_relat_1(sK6)))
    | ~ spl16_4
    | ~ spl16_85 ),
    inference(unit_resulting_resolution,[],[f225,f1113,f1113,f114])).

fof(f1380,plain,
    ( spl16_89
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(avatar_split_clause,[],[f1285,f967,f963,f1377])).

fof(f1285,plain,
    ( r2_hidden(sK15(sK6,sK5,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),sK5)
    | ~ spl16_79
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f964,f969,f92])).

fof(f1332,plain,
    ( ~ spl16_88
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_87 ),
    inference(avatar_split_clause,[],[f1264,f1230,f373,f351,f149,f138,f1329])).

fof(f1264,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_38
    | spl16_87 ),
    inference(unit_resulting_resolution,[],[f1231,f606])).

fof(f1231,plain,
    ( ~ r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k1_relat_1(sK6))
    | spl16_87 ),
    inference(avatar_component_clause,[],[f1230])).

fof(f1233,plain,
    ( spl16_87
    | spl16_79
    | spl16_82 ),
    inference(avatar_split_clause,[],[f1218,f1013,f963,f1230])).

fof(f1218,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),k1_relat_1(sK6))
    | spl16_79
    | spl16_82 ),
    inference(unit_resulting_resolution,[],[f965,f1014,f95])).

fof(f1212,plain,
    ( spl16_86
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_82
    | ~ spl16_84 ),
    inference(avatar_split_clause,[],[f1181,f1035,f1013,f351,f149,f138,f121,f116,f1209])).

fof(f1209,plain,
    ( spl16_86
  <=> r2_hidden(sK11(sK6,sK13(sK6,sK5,k2_relat_1(sK6))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_86])])).

fof(f1035,plain,
    ( spl16_84
  <=> k10_relat_1(k2_funct_1(sK6),sK5) = k2_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_84])])).

fof(f1181,plain,
    ( r2_hidden(sK11(sK6,sK13(sK6,sK5,k2_relat_1(sK6))),sK5)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_35
    | ~ spl16_82
    | ~ spl16_84 ),
    inference(forward_demodulation,[],[f1176,f1147])).

fof(f1147,plain,
    ( k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k2_relat_1(sK6))) = sK11(sK6,sK13(sK6,sK5,k2_relat_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_35
    | ~ spl16_82 ),
    inference(unit_resulting_resolution,[],[f1015,f710])).

fof(f1176,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK6),sK13(sK6,sK5,k2_relat_1(sK6))),sK5)
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_82
    | ~ spl16_84 ),
    inference(unit_resulting_resolution,[],[f1015,f1137])).

fof(f1137,plain,
    ( ! [X1] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK6),X1),sK5)
        | ~ r2_hidden(X1,k2_relat_1(sK6)) )
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_84 ),
    inference(subsumption_resolution,[],[f1136,f140])).

fof(f1136,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK6))
        | r2_hidden(k1_funct_1(k2_funct_1(sK6),X1),sK5)
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_7
    | ~ spl16_84 ),
    inference(subsumption_resolution,[],[f1131,f151])).

fof(f1131,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_relat_1(sK6))
        | r2_hidden(k1_funct_1(k2_funct_1(sK6),X1),sK5)
        | ~ v1_funct_1(k2_funct_1(sK6))
        | ~ v1_relat_1(k2_funct_1(sK6)) )
    | ~ spl16_84 ),
    inference(superposition,[],[f111,f1036])).

fof(f1036,plain,
    ( k10_relat_1(k2_funct_1(sK6),sK5) = k2_relat_1(sK6)
    | ~ spl16_84 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1116,plain,
    ( ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_80
    | spl16_84 ),
    inference(avatar_contradiction_clause,[],[f1115])).

fof(f1115,plain,
    ( $false
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_80
    | spl16_84 ),
    inference(subsumption_resolution,[],[f968,f1043])).

fof(f1043,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_84 ),
    inference(forward_demodulation,[],[f1042,f375])).

fof(f1042,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | ~ spl16_38
    | spl16_84 ),
    inference(subsumption_resolution,[],[f1041,f140])).

fof(f1041,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_7
    | ~ spl16_38
    | spl16_84 ),
    inference(subsumption_resolution,[],[f1040,f151])).

fof(f1040,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_38
    | spl16_84 ),
    inference(subsumption_resolution,[],[f1039,f375])).

fof(f1039,plain,
    ( k1_relat_1(k2_funct_1(sK6)) != k2_relat_1(sK6)
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl16_84 ),
    inference(superposition,[],[f1037,f779])).

fof(f779,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k10_relat_1(X0,X1)
      | r2_hidden(sK12(X0,X1,k1_relat_1(X0)),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(factoring,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),k1_relat_1(X0))
      | k10_relat_1(X0,X1) = X2
      | r2_hidden(sK12(X0,X1,X2),X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1037,plain,
    ( k10_relat_1(k2_funct_1(sK6),sK5) != k2_relat_1(sK6)
    | spl16_84 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f968,plain,
    ( ~ r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | spl16_80 ),
    inference(avatar_component_clause,[],[f967])).

fof(f1114,plain,
    ( spl16_85
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_80 ),
    inference(avatar_split_clause,[],[f1065,f967,f121,f116,f1111])).

fof(f1065,plain,
    ( r2_hidden(sK11(sK6,sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6))),k1_relat_1(sK6))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_80 ),
    inference(unit_resulting_resolution,[],[f118,f123,f969,f109])).

fof(f1038,plain,
    ( ~ spl16_84
    | spl16_6
    | ~ spl16_81 ),
    inference(avatar_split_clause,[],[f1023,f1007,f144,f1035])).

fof(f1023,plain,
    ( k10_relat_1(k2_funct_1(sK6),sK5) != k2_relat_1(sK6)
    | spl16_6
    | ~ spl16_81 ),
    inference(backward_demodulation,[],[f146,f1008])).

fof(f1022,plain,
    ( ~ spl16_4
    | ~ spl16_79
    | spl16_81 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_79
    | spl16_81 ),
    inference(subsumption_resolution,[],[f964,f1011])).

fof(f1011,plain,
    ( ~ sP3(sK6,sK5,k2_relat_1(sK6))
    | ~ spl16_4
    | spl16_81 ),
    inference(unit_resulting_resolution,[],[f135,f1009,f90])).

fof(f1020,plain,
    ( spl16_82
    | spl16_83
    | spl16_79 ),
    inference(avatar_split_clause,[],[f986,f963,f1017,f1013])).

fof(f1017,plain,
    ( spl16_83
  <=> r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_83])])).

fof(f986,plain,
    ( r2_hidden(sK14(sK6,sK5,k2_relat_1(sK6)),sK5)
    | r2_hidden(sK13(sK6,sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | spl16_79 ),
    inference(resolution,[],[f965,f96])).

fof(f1010,plain,
    ( ~ spl16_81
    | spl16_80
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(avatar_split_clause,[],[f961,f373,f149,f144,f138,f967,f1007])).

fof(f961,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | k9_relat_1(sK6,sK5) != k2_relat_1(sK6)
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(forward_demodulation,[],[f960,f375])).

fof(f960,plain,
    ( k9_relat_1(sK6,sK5) != k2_relat_1(sK6)
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7
    | ~ spl16_38 ),
    inference(forward_demodulation,[],[f959,f375])).

fof(f959,plain,
    ( k9_relat_1(sK6,sK5) != k1_relat_1(k2_funct_1(sK6))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | spl16_6
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f958,f140])).

fof(f958,plain,
    ( k9_relat_1(sK6,sK5) != k1_relat_1(k2_funct_1(sK6))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl16_6
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f947,f151])).

fof(f947,plain,
    ( k9_relat_1(sK6,sK5) != k1_relat_1(k2_funct_1(sK6))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl16_6 ),
    inference(superposition,[],[f146,f779])).

fof(f970,plain,
    ( ~ spl16_79
    | spl16_80
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_38 ),
    inference(avatar_split_clause,[],[f957,f373,f297,f149,f138,f967,f963])).

fof(f957,plain,
    ( r2_hidden(sK12(k2_funct_1(sK6),sK5,k2_relat_1(sK6)),k2_relat_1(sK6))
    | ~ sP3(sK6,sK5,k2_relat_1(sK6))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_38 ),
    inference(forward_demodulation,[],[f956,f375])).

fof(f956,plain,
    ( ~ sP3(sK6,sK5,k2_relat_1(sK6))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29
    | ~ spl16_38 ),
    inference(forward_demodulation,[],[f955,f375])).

fof(f955,plain,
    ( ~ sP3(sK6,sK5,k1_relat_1(k2_funct_1(sK6)))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7
    | spl16_29 ),
    inference(subsumption_resolution,[],[f954,f140])).

fof(f954,plain,
    ( ~ sP3(sK6,sK5,k1_relat_1(k2_funct_1(sK6)))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_7
    | spl16_29 ),
    inference(subsumption_resolution,[],[f946,f151])).

fof(f946,plain,
    ( ~ sP3(sK6,sK5,k1_relat_1(k2_funct_1(sK6)))
    | r2_hidden(sK12(k2_funct_1(sK6),sK5,k1_relat_1(k2_funct_1(sK6))),k1_relat_1(k2_funct_1(sK6)))
    | ~ v1_funct_1(k2_funct_1(sK6))
    | ~ v1_relat_1(k2_funct_1(sK6))
    | spl16_29 ),
    inference(superposition,[],[f299,f779])).

fof(f944,plain,
    ( spl16_78
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(avatar_split_clause,[],[f936,f924,f919,f941])).

fof(f941,plain,
    ( spl16_78
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_78])])).

fof(f936,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))
    | ~ spl16_75
    | ~ spl16_76 ),
    inference(unit_resulting_resolution,[],[f921,f926,f99])).

fof(f932,plain,
    ( spl16_77
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(avatar_split_clause,[],[f821,f807,f802,f126,f121,f116,f929])).

fof(f929,plain,
    ( spl16_77
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_77])])).

fof(f802,plain,
    ( spl16_69
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_69])])).

fof(f807,plain,
    ( spl16_70
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_70])])).

fof(f821,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(unit_resulting_resolution,[],[f804,f809,f335])).

fof(f809,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))
    | ~ spl16_70 ),
    inference(avatar_component_clause,[],[f807])).

fof(f804,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))
    | ~ spl16_69 ),
    inference(avatar_component_clause,[],[f802])).

fof(f927,plain,
    ( spl16_76
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(avatar_split_clause,[],[f818,f807,f802,f924])).

fof(f818,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(unit_resulting_resolution,[],[f804,f809,f61])).

fof(f922,plain,
    ( spl16_75
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(avatar_split_clause,[],[f817,f807,f802,f919])).

fof(f817,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))))
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(unit_resulting_resolution,[],[f804,f809,f60])).

fof(f863,plain,
    ( spl16_73
    | ~ spl16_74
    | ~ spl16_42 ),
    inference(avatar_split_clause,[],[f415,f409,f860,f856])).

fof(f856,plain,
    ( spl16_73
  <=> k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_73])])).

fof(f860,plain,
    ( spl16_74
  <=> sP1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_74])])).

fof(f409,plain,
    ( spl16_42
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_42])])).

fof(f415,plain,
    ( ~ sP1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))),sK6)
    | k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_42 ),
    inference(resolution,[],[f411,f63])).

fof(f411,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_42 ),
    inference(avatar_component_clause,[],[f409])).

fof(f827,plain,
    ( spl16_72
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(avatar_split_clause,[],[f820,f807,f802,f824])).

fof(f824,plain,
    ( spl16_72
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_72])])).

fof(f820,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))
    | ~ spl16_69
    | ~ spl16_70 ),
    inference(unit_resulting_resolution,[],[f804,f809,f99])).

fof(f815,plain,
    ( spl16_71
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(avatar_split_clause,[],[f689,f668,f663,f126,f121,f116,f812])).

fof(f812,plain,
    ( spl16_71
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_71])])).

fof(f663,plain,
    ( spl16_65
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_65])])).

fof(f668,plain,
    ( spl16_66
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_66])])).

fof(f689,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(unit_resulting_resolution,[],[f665,f670,f335])).

fof(f670,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))
    | ~ spl16_66 ),
    inference(avatar_component_clause,[],[f668])).

fof(f665,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))
    | ~ spl16_65 ),
    inference(avatar_component_clause,[],[f663])).

fof(f810,plain,
    ( spl16_70
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(avatar_split_clause,[],[f686,f668,f663,f807])).

fof(f686,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(unit_resulting_resolution,[],[f665,f670,f61])).

fof(f805,plain,
    ( spl16_69
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(avatar_split_clause,[],[f685,f668,f663,f802])).

fof(f685,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))))
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(unit_resulting_resolution,[],[f665,f670,f60])).

fof(f695,plain,
    ( spl16_68
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(avatar_split_clause,[],[f688,f668,f663,f692])).

fof(f692,plain,
    ( spl16_68
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_68])])).

fof(f688,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))
    | ~ spl16_65
    | ~ spl16_66 ),
    inference(unit_resulting_resolution,[],[f665,f670,f99])).

fof(f676,plain,
    ( spl16_67
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(avatar_split_clause,[],[f573,f560,f551,f126,f121,f116,f673])).

fof(f673,plain,
    ( spl16_67
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_67])])).

fof(f551,plain,
    ( spl16_59
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_59])])).

fof(f560,plain,
    ( spl16_60
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_60])])).

fof(f573,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(unit_resulting_resolution,[],[f553,f562,f335])).

fof(f562,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))
    | ~ spl16_60 ),
    inference(avatar_component_clause,[],[f560])).

fof(f553,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))
    | ~ spl16_59 ),
    inference(avatar_component_clause,[],[f551])).

fof(f671,plain,
    ( spl16_66
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(avatar_split_clause,[],[f570,f560,f551,f668])).

fof(f570,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(unit_resulting_resolution,[],[f553,f562,f61])).

fof(f666,plain,
    ( spl16_65
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(avatar_split_clause,[],[f569,f560,f551,f663])).

fof(f569,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))))
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(unit_resulting_resolution,[],[f553,f562,f60])).

fof(f591,plain,
    ( spl16_63
    | ~ spl16_64
    | ~ spl16_41 ),
    inference(avatar_split_clause,[],[f407,f403,f588,f584])).

fof(f584,plain,
    ( spl16_63
  <=> k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_63])])).

fof(f588,plain,
    ( spl16_64
  <=> sP1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_64])])).

fof(f403,plain,
    ( spl16_41
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_41])])).

fof(f407,plain,
    ( ~ sP1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))),sK6)
    | k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_41 ),
    inference(resolution,[],[f405,f63])).

fof(f405,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_41 ),
    inference(avatar_component_clause,[],[f403])).

fof(f581,plain,
    ( spl16_62
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(avatar_split_clause,[],[f572,f560,f551,f578])).

fof(f578,plain,
    ( spl16_62
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_62])])).

fof(f572,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))
    | ~ spl16_59
    | ~ spl16_60 ),
    inference(unit_resulting_resolution,[],[f553,f562,f99])).

fof(f568,plain,
    ( spl16_61
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(avatar_split_clause,[],[f538,f517,f512,f126,f121,f116,f565])).

fof(f565,plain,
    ( spl16_61
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_61])])).

fof(f512,plain,
    ( spl16_55
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_55])])).

fof(f517,plain,
    ( spl16_56
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_56])])).

fof(f538,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(unit_resulting_resolution,[],[f514,f519,f335])).

fof(f519,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))
    | ~ spl16_56 ),
    inference(avatar_component_clause,[],[f517])).

fof(f514,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))
    | ~ spl16_55 ),
    inference(avatar_component_clause,[],[f512])).

fof(f563,plain,
    ( spl16_60
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(avatar_split_clause,[],[f535,f517,f512,f560])).

fof(f535,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(unit_resulting_resolution,[],[f514,f519,f61])).

fof(f554,plain,
    ( spl16_59
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(avatar_split_clause,[],[f534,f517,f512,f551])).

fof(f534,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))))
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(unit_resulting_resolution,[],[f514,f519,f60])).

fof(f546,plain,
    ( spl16_58
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(avatar_split_clause,[],[f537,f517,f512,f543])).

fof(f543,plain,
    ( spl16_58
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_58])])).

fof(f537,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))
    | ~ spl16_55
    | ~ spl16_56 ),
    inference(unit_resulting_resolution,[],[f514,f519,f99])).

fof(f533,plain,
    ( spl16_57
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(avatar_split_clause,[],[f486,f472,f467,f126,f121,f116,f530])).

fof(f530,plain,
    ( spl16_57
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_57])])).

fof(f467,plain,
    ( spl16_49
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_49])])).

fof(f472,plain,
    ( spl16_50
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_50])])).

fof(f486,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(unit_resulting_resolution,[],[f469,f474,f335])).

fof(f474,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))
    | ~ spl16_50 ),
    inference(avatar_component_clause,[],[f472])).

fof(f469,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))
    | ~ spl16_49 ),
    inference(avatar_component_clause,[],[f467])).

fof(f520,plain,
    ( spl16_56
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(avatar_split_clause,[],[f483,f472,f467,f517])).

fof(f483,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(unit_resulting_resolution,[],[f469,f474,f61])).

fof(f515,plain,
    ( spl16_55
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(avatar_split_clause,[],[f482,f472,f467,f512])).

fof(f482,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))))
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(unit_resulting_resolution,[],[f469,f474,f60])).

fof(f502,plain,
    ( spl16_53
    | ~ spl16_54
    | ~ spl16_37 ),
    inference(avatar_split_clause,[],[f377,f368,f499,f495])).

fof(f495,plain,
    ( spl16_53
  <=> k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_53])])).

fof(f499,plain,
    ( spl16_54
  <=> sP1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_54])])).

fof(f368,plain,
    ( spl16_37
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_37])])).

fof(f377,plain,
    ( ~ sP1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))),sK6)
    | k2_funct_1(sK6) = k2_funct_1(k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_37 ),
    inference(resolution,[],[f370,f63])).

fof(f370,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_37 ),
    inference(avatar_component_clause,[],[f368])).

fof(f492,plain,
    ( spl16_52
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(avatar_split_clause,[],[f485,f472,f467,f489])).

fof(f489,plain,
    ( spl16_52
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_52])])).

fof(f485,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))
    | ~ spl16_49
    | ~ spl16_50 ),
    inference(unit_resulting_resolution,[],[f469,f474,f99])).

fof(f480,plain,
    ( spl16_51
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(avatar_split_clause,[],[f332,f316,f311,f126,f121,f116,f477])).

fof(f477,plain,
    ( spl16_51
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_51])])).

fof(f311,plain,
    ( spl16_31
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_31])])).

fof(f316,plain,
    ( spl16_32
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_32])])).

fof(f332,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(unit_resulting_resolution,[],[f313,f318,f118,f123,f128,f76])).

fof(f318,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))
    | ~ spl16_32 ),
    inference(avatar_component_clause,[],[f316])).

fof(f313,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))
    | ~ spl16_31 ),
    inference(avatar_component_clause,[],[f311])).

fof(f475,plain,
    ( spl16_50
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(avatar_split_clause,[],[f321,f316,f311,f472])).

fof(f321,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(unit_resulting_resolution,[],[f313,f318,f60])).

fof(f470,plain,
    ( spl16_49
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(avatar_split_clause,[],[f320,f316,f311,f467])).

fof(f320,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))))
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(unit_resulting_resolution,[],[f313,f318,f61])).

fof(f453,plain,
    ( spl16_48
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(avatar_split_clause,[],[f322,f316,f311,f450])).

fof(f450,plain,
    ( spl16_48
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).

fof(f322,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))
    | ~ spl16_31
    | ~ spl16_32 ),
    inference(unit_resulting_resolution,[],[f313,f318,f99])).

fof(f447,plain,
    ( spl16_47
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(avatar_split_clause,[],[f331,f283,f278,f126,f121,f116,f444])).

fof(f444,plain,
    ( spl16_47
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_47])])).

fof(f278,plain,
    ( spl16_27
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_27])])).

fof(f283,plain,
    ( spl16_28
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_28])])).

fof(f331,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(unit_resulting_resolution,[],[f280,f285,f118,f123,f128,f76])).

fof(f285,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))
    | ~ spl16_28 ),
    inference(avatar_component_clause,[],[f283])).

fof(f280,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))
    | ~ spl16_27 ),
    inference(avatar_component_clause,[],[f278])).

fof(f440,plain,
    ( spl16_45
    | ~ spl16_46
    | ~ spl16_36 ),
    inference(avatar_split_clause,[],[f366,f362,f437,f433])).

fof(f433,plain,
    ( spl16_45
  <=> k2_funct_1(sK6) = k2_funct_1(k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_45])])).

fof(f437,plain,
    ( spl16_46
  <=> sP1(k2_funct_1(k2_funct_1(sK6)),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_46])])).

fof(f362,plain,
    ( spl16_36
  <=> sP2(sK6,k2_funct_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_36])])).

fof(f366,plain,
    ( ~ sP1(k2_funct_1(k2_funct_1(sK6)),sK6)
    | k2_funct_1(sK6) = k2_funct_1(k2_funct_1(sK6))
    | ~ spl16_36 ),
    inference(resolution,[],[f364,f63])).

fof(f364,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_36 ),
    inference(avatar_component_clause,[],[f362])).

fof(f426,plain,
    ( spl16_44
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(avatar_split_clause,[],[f330,f264,f259,f126,f121,f116,f423])).

fof(f423,plain,
    ( spl16_44
  <=> sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_44])])).

fof(f259,plain,
    ( spl16_24
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_24])])).

fof(f264,plain,
    ( spl16_25
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_25])])).

fof(f330,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(unit_resulting_resolution,[],[f261,f266,f118,f123,f128,f76])).

fof(f266,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))
    | ~ spl16_25 ),
    inference(avatar_component_clause,[],[f264])).

fof(f261,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))
    | ~ spl16_24 ),
    inference(avatar_component_clause,[],[f259])).

fof(f420,plain,
    ( spl16_43
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f329,f245,f240,f126,f121,f116,f417])).

fof(f240,plain,
    ( spl16_21
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_21])])).

fof(f245,plain,
    ( spl16_22
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_22])])).

fof(f329,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(unit_resulting_resolution,[],[f242,f247,f118,f123,f128,f76])).

fof(f247,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f242,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_21 ),
    inference(avatar_component_clause,[],[f240])).

fof(f412,plain,
    ( spl16_42
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(avatar_split_clause,[],[f328,f221,f216,f126,f121,f116,f409])).

fof(f216,plain,
    ( spl16_18
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_18])])).

fof(f221,plain,
    ( spl16_19
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_19])])).

fof(f328,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(unit_resulting_resolution,[],[f218,f223,f118,f123,f128,f76])).

fof(f223,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f218,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_18 ),
    inference(avatar_component_clause,[],[f216])).

fof(f406,plain,
    ( spl16_41
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f327,f203,f198,f126,f121,f116,f403])).

fof(f198,plain,
    ( spl16_15
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_15])])).

fof(f203,plain,
    ( spl16_16
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_16])])).

fof(f327,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(unit_resulting_resolution,[],[f200,f205,f118,f123,f128,f76])).

fof(f205,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_16 ),
    inference(avatar_component_clause,[],[f203])).

fof(f200,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_15 ),
    inference(avatar_component_clause,[],[f198])).

fof(f399,plain,
    ( spl16_39
    | ~ spl16_40
    | ~ spl16_33 ),
    inference(avatar_split_clause,[],[f341,f337,f396,f392])).

fof(f392,plain,
    ( spl16_39
  <=> sK6 = k2_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_39])])).

fof(f396,plain,
    ( spl16_40
  <=> sP1(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_40])])).

fof(f337,plain,
    ( spl16_33
  <=> sP2(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_33])])).

fof(f341,plain,
    ( ~ sP1(sK6,sK6)
    | sK6 = k2_funct_1(sK6)
    | ~ spl16_33 ),
    inference(resolution,[],[f339,f63])).

fof(f339,plain,
    ( sP2(sK6,sK6)
    | ~ spl16_33 ),
    inference(avatar_component_clause,[],[f337])).

fof(f376,plain,
    ( spl16_38
    | ~ spl16_35 ),
    inference(avatar_split_clause,[],[f358,f351,f373])).

fof(f358,plain,
    ( k1_relat_1(k2_funct_1(sK6)) = k2_relat_1(sK6)
    | ~ spl16_35 ),
    inference(unit_resulting_resolution,[],[f353,f64])).

fof(f371,plain,
    ( spl16_37
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f326,f185,f180,f126,f121,f116,f368])).

fof(f180,plain,
    ( spl16_12
  <=> v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_12])])).

fof(f185,plain,
    ( spl16_13
  <=> v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f326,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f182,f187,f118,f123,f128,f76])).

fof(f187,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_13 ),
    inference(avatar_component_clause,[],[f185])).

fof(f182,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f365,plain,
    ( spl16_36
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f325,f167,f162,f126,f121,f116,f362])).

fof(f162,plain,
    ( spl16_9
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_9])])).

fof(f167,plain,
    ( spl16_10
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f325,plain,
    ( sP2(sK6,k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f164,f169,f118,f123,f128,f76])).

fof(f169,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f167])).

fof(f164,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_9 ),
    inference(avatar_component_clause,[],[f162])).

fof(f354,plain,
    ( spl16_35
    | ~ spl16_34 ),
    inference(avatar_split_clause,[],[f347,f343,f351])).

fof(f343,plain,
    ( spl16_34
  <=> sP2(sK6,k2_funct_1(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_34])])).

fof(f347,plain,
    ( sP1(k2_funct_1(sK6),sK6)
    | ~ spl16_34 ),
    inference(unit_resulting_resolution,[],[f345,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ sP2(X0,k2_funct_1(X0))
      | sP1(k2_funct_1(X0),X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | k2_funct_1(X0) != X1
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f345,plain,
    ( sP2(sK6,k2_funct_1(sK6))
    | ~ spl16_34 ),
    inference(avatar_component_clause,[],[f343])).

fof(f346,plain,
    ( spl16_34
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f324,f149,f138,f126,f121,f116,f343])).

fof(f324,plain,
    ( sP2(sK6,k2_funct_1(sK6))
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(unit_resulting_resolution,[],[f151,f140,f118,f123,f128,f76])).

fof(f340,plain,
    ( spl16_33
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3 ),
    inference(avatar_split_clause,[],[f323,f126,f121,f116,f337])).

fof(f323,plain,
    ( sP2(sK6,sK6)
    | ~ spl16_1
    | ~ spl16_2
    | ~ spl16_3 ),
    inference(unit_resulting_resolution,[],[f123,f118,f118,f123,f128,f76])).

fof(f319,plain,
    ( spl16_32
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(avatar_split_clause,[],[f302,f283,f278,f316])).

fof(f302,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(unit_resulting_resolution,[],[f280,f285,f60])).

fof(f314,plain,
    ( spl16_31
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(avatar_split_clause,[],[f301,f283,f278,f311])).

fof(f301,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))))
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(unit_resulting_resolution,[],[f280,f285,f61])).

fof(f308,plain,
    ( spl16_30
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(avatar_split_clause,[],[f303,f283,f278,f305])).

fof(f305,plain,
    ( spl16_30
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_30])])).

fof(f303,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))
    | ~ spl16_27
    | ~ spl16_28 ),
    inference(unit_resulting_resolution,[],[f280,f285,f99])).

fof(f300,plain,
    ( ~ spl16_29
    | ~ spl16_4
    | spl16_6 ),
    inference(avatar_split_clause,[],[f290,f144,f133,f297])).

fof(f290,plain,
    ( ~ sP3(sK6,sK5,k10_relat_1(k2_funct_1(sK6),sK5))
    | ~ spl16_4
    | spl16_6 ),
    inference(unit_resulting_resolution,[],[f135,f146,f90])).

fof(f286,plain,
    ( spl16_28
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(avatar_split_clause,[],[f269,f264,f259,f283])).

fof(f269,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(unit_resulting_resolution,[],[f261,f266,f60])).

fof(f281,plain,
    ( spl16_27
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(avatar_split_clause,[],[f268,f264,f259,f278])).

fof(f268,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))))
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(unit_resulting_resolution,[],[f261,f266,f61])).

fof(f275,plain,
    ( spl16_26
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(avatar_split_clause,[],[f270,f264,f259,f272])).

fof(f272,plain,
    ( spl16_26
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_26])])).

fof(f270,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))
    | ~ spl16_24
    | ~ spl16_25 ),
    inference(unit_resulting_resolution,[],[f261,f266,f99])).

fof(f267,plain,
    ( spl16_25
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f250,f245,f240,f264])).

fof(f250,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(unit_resulting_resolution,[],[f242,f247,f60])).

fof(f262,plain,
    ( spl16_24
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f249,f245,f240,f259])).

fof(f249,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))))
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(unit_resulting_resolution,[],[f242,f247,f61])).

fof(f256,plain,
    ( spl16_23
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(avatar_split_clause,[],[f251,f245,f240,f253])).

fof(f253,plain,
    ( spl16_23
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_23])])).

fof(f251,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_21
    | ~ spl16_22 ),
    inference(unit_resulting_resolution,[],[f242,f247,f99])).

fof(f248,plain,
    ( spl16_22
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(avatar_split_clause,[],[f231,f221,f216,f245])).

fof(f231,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(unit_resulting_resolution,[],[f218,f223,f60])).

fof(f243,plain,
    ( spl16_21
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(avatar_split_clause,[],[f230,f221,f216,f240])).

fof(f230,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))))
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(unit_resulting_resolution,[],[f218,f223,f61])).

fof(f237,plain,
    ( spl16_20
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(avatar_split_clause,[],[f232,f221,f216,f234])).

fof(f234,plain,
    ( spl16_20
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_20])])).

fof(f232,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_18
    | ~ spl16_19 ),
    inference(unit_resulting_resolution,[],[f218,f223,f99])).

fof(f224,plain,
    ( spl16_19
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f208,f203,f198,f221])).

fof(f208,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(unit_resulting_resolution,[],[f200,f205,f60])).

fof(f219,plain,
    ( spl16_18
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f207,f203,f198,f216])).

fof(f207,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))))
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(unit_resulting_resolution,[],[f200,f205,f61])).

fof(f214,plain,
    ( spl16_17
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(avatar_split_clause,[],[f209,f203,f198,f211])).

fof(f211,plain,
    ( spl16_17
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_17])])).

fof(f209,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_15
    | ~ spl16_16 ),
    inference(unit_resulting_resolution,[],[f200,f205,f99])).

fof(f206,plain,
    ( spl16_16
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f190,f185,f180,f203])).

fof(f190,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f182,f187,f60])).

fof(f201,plain,
    ( spl16_15
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f189,f185,f180,f198])).

fof(f189,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))))
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f182,f187,f61])).

fof(f196,plain,
    ( spl16_14
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f191,f185,f180,f193])).

fof(f193,plain,
    ( spl16_14
  <=> sP4(k2_funct_1(k2_funct_1(k2_funct_1(sK6)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_14])])).

fof(f191,plain,
    ( sP4(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_12
    | ~ spl16_13 ),
    inference(unit_resulting_resolution,[],[f182,f187,f99])).

fof(f188,plain,
    ( spl16_13
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f172,f167,f162,f185])).

fof(f172,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f164,f169,f60])).

fof(f183,plain,
    ( spl16_12
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f171,f167,f162,f180])).

fof(f171,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK6))))
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f164,f169,f61])).

fof(f178,plain,
    ( spl16_11
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(avatar_split_clause,[],[f173,f167,f162,f175])).

fof(f175,plain,
    ( spl16_11
  <=> sP4(k2_funct_1(k2_funct_1(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f173,plain,
    ( sP4(k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_9
    | ~ spl16_10 ),
    inference(unit_resulting_resolution,[],[f164,f169,f99])).

fof(f170,plain,
    ( spl16_10
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f154,f149,f138,f167])).

fof(f154,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(unit_resulting_resolution,[],[f140,f151,f60])).

fof(f165,plain,
    ( spl16_9
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f153,f149,f138,f162])).

fof(f153,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK6)))
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(unit_resulting_resolution,[],[f140,f151,f61])).

fof(f160,plain,
    ( spl16_8
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f155,f149,f138,f157])).

fof(f155,plain,
    ( sP4(k2_funct_1(sK6))
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(unit_resulting_resolution,[],[f140,f151,f99])).

fof(f152,plain,
    ( spl16_7
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f142,f121,f116,f149])).

fof(f142,plain,
    ( v1_funct_1(k2_funct_1(sK6))
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(unit_resulting_resolution,[],[f118,f123,f61])).

fof(f147,plain,(
    ~ spl16_6 ),
    inference(avatar_split_clause,[],[f59,f144])).

fof(f59,plain,(
    k9_relat_1(sK6,sK5) != k10_relat_1(k2_funct_1(sK6),sK5) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( k9_relat_1(sK6,sK5) != k10_relat_1(k2_funct_1(sK6),sK5)
    & v2_funct_1(sK6)
    & v1_funct_1(sK6)
    & v1_relat_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f9,f27])).

fof(f27,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
        & v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k9_relat_1(sK6,sK5) != k10_relat_1(k2_funct_1(sK6),sK5)
      & v2_funct_1(sK6)
      & v1_funct_1(sK6)
      & v1_relat_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( k9_relat_1(X1,X0) != k10_relat_1(k2_funct_1(X1),X0)
      & v2_funct_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( v2_funct_1(X1)
         => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

fof(f141,plain,
    ( spl16_5
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f131,f121,f116,f138])).

fof(f131,plain,
    ( v1_relat_1(k2_funct_1(sK6))
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(unit_resulting_resolution,[],[f118,f123,f60])).

fof(f136,plain,
    ( spl16_4
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(avatar_split_clause,[],[f130,f121,f116,f133])).

fof(f130,plain,
    ( sP4(sK6)
    | ~ spl16_1
    | ~ spl16_2 ),
    inference(unit_resulting_resolution,[],[f118,f123,f99])).

fof(f129,plain,(
    spl16_3 ),
    inference(avatar_split_clause,[],[f58,f126])).

fof(f58,plain,(
    v2_funct_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f124,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f57,f121])).

fof(f57,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

fof(f119,plain,(
    spl16_1 ),
    inference(avatar_split_clause,[],[f56,f116])).

fof(f56,plain,(
    v1_relat_1(sK6) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
