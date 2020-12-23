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
% DateTime   : Thu Dec  3 12:52:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 166 expanded)
%              Number of leaves         :   23 (  72 expanded)
%              Depth                    :   10
%              Number of atoms          :  275 ( 498 expanded)
%              Number of equality atoms :   83 ( 148 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f353,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f99,f115,f138,f164,f176,f255,f349])).

fof(f349,plain,
    ( spl1_1
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f348,f170,f134,f74,f67,f48])).

fof(f48,plain,
    ( spl1_1
  <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f67,plain,
    ( spl1_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f74,plain,
    ( spl1_6
  <=> v1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f134,plain,
    ( spl1_12
  <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f170,plain,
    ( spl1_18
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f348,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_12
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f347,f136])).

fof(f136,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f347,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_18 ),
    inference(forward_demodulation,[],[f289,f172])).

fof(f172,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f289,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f76,f69,f45,f41,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X0) != k1_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X0) = k1_relat_1(X1)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f45,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f69,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f76,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f255,plain,
    ( spl1_2
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_11
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f254,f160,f112,f74,f67,f52])).

fof(f52,plain,
    ( spl1_2
  <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f112,plain,
    ( spl1_11
  <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f160,plain,
    ( spl1_16
  <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f254,plain,
    ( k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_11
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f253,f114])).

fof(f114,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f253,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5
    | ~ spl1_6
    | ~ spl1_16 ),
    inference(forward_demodulation,[],[f252,f162])).

fof(f162,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f252,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f251,f117])).

fof(f117,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f251,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f183,f121])).

fof(f121,plain,
    ( ! [X0] : k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f183,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0))
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f69,f76,f45,f42,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k2_relat_1(X0) != k2_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f176,plain,
    ( spl1_18
    | ~ spl1_9
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f174,f160,f96,f170])).

fof(f96,plain,
    ( spl1_9
  <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f174,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))
    | ~ spl1_9
    | ~ spl1_16 ),
    inference(backward_demodulation,[],[f98,f162])).

fof(f98,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f164,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_16
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f158,f57,f160,f62,f67])).

fof(f62,plain,
    ( spl1_4
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f57,plain,
    ( spl1_3
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f158,plain,
    ( k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f36,f59])).

fof(f59,plain,
    ( v2_funct_1(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f57])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f138,plain,
    ( ~ spl1_5
    | ~ spl1_4
    | spl1_12
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f132,f57,f134,f62,f67])).

fof(f132,plain,
    ( k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ spl1_3 ),
    inference(resolution,[],[f35,f59])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,
    ( spl1_11
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f100,f67,f112])).

fof(f100,plain,
    ( k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f99,plain,
    ( spl1_9
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f94,f74,f96])).

fof(f94,plain,
    ( k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f76,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f77,plain,
    ( spl1_6
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f71,f67,f62,f74])).

fof(f71,plain,
    ( v1_relat_1(k2_funct_1(sK0))
    | ~ spl1_4
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f69,f64,f43])).

fof(f43,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f64,plain,
    ( v1_funct_1(sK0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
      | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
        | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) )
      & v2_funct_1(sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ( k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
            & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f65,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f31,f57])).

fof(f31,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,
    ( ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f32,f52,f48])).

fof(f32,plain,
    ( k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))
    | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:26:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (9098)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.46  % (9098)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (9109)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f353,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f99,f115,f138,f164,f176,f255,f349])).
% 0.20/0.48  fof(f349,plain,(
% 0.20/0.48    spl1_1 | ~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_18),
% 0.20/0.48    inference(avatar_split_clause,[],[f348,f170,f134,f74,f67,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl1_1 <=> k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    spl1_5 <=> v1_relat_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl1_6 <=> v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    spl1_12 <=> k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.48  fof(f170,plain,(
% 0.20/0.48    spl1_18 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.48  fof(f348,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_12 | ~spl1_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f347,f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~spl1_12),
% 0.20/0.48    inference(avatar_component_clause,[],[f134])).
% 0.20/0.48  fof(f347,plain,(
% 0.20/0.48    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k2_funct_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_18)),
% 0.20/0.48    inference(forward_demodulation,[],[f289,f172])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | ~spl1_18),
% 0.20/0.48    inference(avatar_component_clause,[],[f170])).
% 0.20/0.48  fof(f289,plain,(
% 0.20/0.48    k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k1_relat_1(k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f76,f69,f45,f41,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k1_relat_1(X0) != k1_relat_1(X1) | k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) | k1_relat_1(X0) != k1_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k1_relat_1(X0) = k1_relat_1(X1) => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    v1_relat_1(sK0) | ~spl1_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f67])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK0)) | ~spl1_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f74])).
% 0.20/0.48  fof(f255,plain,(
% 0.20/0.48    spl1_2 | ~spl1_5 | ~spl1_6 | ~spl1_11 | ~spl1_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f254,f160,f112,f74,f67,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    spl1_2 <=> k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl1_11 <=> k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    spl1_16 <=> k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_11 | ~spl1_16)),
% 0.20/0.48    inference(forward_demodulation,[],[f253,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f112])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k1_relat_1(sK0)) | (~spl1_5 | ~spl1_6 | ~spl1_16)),
% 0.20/0.48    inference(forward_demodulation,[],[f252,f162])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | ~spl1_16),
% 0.20/0.48    inference(avatar_component_clause,[],[f160])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k9_relat_1(sK0,k2_relat_1(k2_funct_1(sK0))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f251,f117])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl1_5),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.48  fof(f251,plain,(
% 0.20/0.48    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k7_relat_1(sK0,k2_relat_1(k2_funct_1(sK0)))) | (~spl1_5 | ~spl1_6)),
% 0.20/0.48    inference(forward_demodulation,[],[f183,f121])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X0] : (k7_relat_1(sK0,X0) = k5_relat_1(k6_relat_1(X0),sK0)) ) | ~spl1_5),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.20/0.48  fof(f183,plain,(
% 0.20/0.48    k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(k2_funct_1(sK0))),sK0)) | (~spl1_5 | ~spl1_6)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f76,f45,f42,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k2_relat_1(X0) != k2_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : (k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) | k2_relat_1(X0) != k2_relat_1(X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k2_relat_1(X0) = k2_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f176,plain,(
% 0.20/0.48    spl1_18 | ~spl1_9 | ~spl1_16),
% 0.20/0.48    inference(avatar_split_clause,[],[f174,f160,f96,f170])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl1_9 <=> k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) | (~spl1_9 | ~spl1_16)),
% 0.20/0.48    inference(backward_demodulation,[],[f98,f162])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f164,plain,(
% 0.20/0.48    ~spl1_5 | ~spl1_4 | spl1_16 | ~spl1_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f158,f57,f160,f62,f67])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    spl1_4 <=> v1_funct_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl1_3 <=> v2_funct_1(sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.48  fof(f158,plain,(
% 0.20/0.48    k2_relat_1(k2_funct_1(sK0)) = k1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.48    inference(resolution,[],[f36,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    v2_funct_1(sK0) | ~spl1_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f57])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    ~spl1_5 | ~spl1_4 | spl1_12 | ~spl1_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f132,f57,f134,f62,f67])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k1_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | ~spl1_3),
% 0.20/0.48    inference(resolution,[],[f35,f59])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f115,plain,(
% 0.20/0.48    spl1_11 | ~spl1_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f100,f67,f112])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    k2_relat_1(sK0) = k9_relat_1(sK0,k1_relat_1(sK0)) | ~spl1_5),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl1_9 | ~spl1_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f94,f74,f96])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) | ~spl1_6),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f76,f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    spl1_6 | ~spl1_4 | ~spl1_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f71,f67,f62,f74])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    v1_relat_1(k2_funct_1(sK0)) | (~spl1_4 | ~spl1_5)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f69,f64,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    v1_funct_1(sK0) | ~spl1_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f62])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl1_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f67])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v1_relat_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    (k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f14,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => ((k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))) & v2_funct_1(sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0] : ((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (((k2_relat_1(X0) != k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | k2_relat_1(X0) != k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    spl1_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f62])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    v1_funct_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    spl1_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f57])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v2_funct_1(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ~spl1_1 | ~spl1_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f52,f48])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    k2_relat_1(sK0) != k2_relat_1(k5_relat_1(k2_funct_1(sK0),sK0)) | k2_relat_1(sK0) != k1_relat_1(k5_relat_1(k2_funct_1(sK0),sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (9098)------------------------------
% 0.20/0.48  % (9098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (9098)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (9098)Memory used [KB]: 10874
% 0.20/0.48  % (9098)Time elapsed: 0.063 s
% 0.20/0.48  % (9098)------------------------------
% 0.20/0.48  % (9098)------------------------------
% 0.20/0.48  % (9091)Success in time 0.129 s
%------------------------------------------------------------------------------
