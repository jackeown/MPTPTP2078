%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0797+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:40 EST 2020

% Result     : Theorem 3.86s
% Output     : Refutation 3.86s
% Verified   : 
% Statistics : Number of formulae       :  334 (1106 expanded)
%              Number of leaves         :   38 ( 369 expanded)
%              Depth                    :   21
%              Number of atoms          : 1911 (4885 expanded)
%              Number of equality atoms :  158 ( 660 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f73,f78,f83,f116,f121,f126,f150,f159,f167,f192,f208,f232,f238,f251,f292,f298,f315,f2168,f2216,f3382,f3449,f3491,f3703,f3798,f3843,f3895,f3961,f3976,f4063,f4150,f4213])).

fof(f4213,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | ~ spl9_50
    | ~ spl9_58
    | spl9_72 ),
    inference(avatar_contradiction_clause,[],[f4212])).

fof(f4212,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | ~ spl9_50
    | ~ spl9_58
    | spl9_72 ),
    inference(subsumption_resolution,[],[f4211,f3195])).

fof(f3195,plain,
    ( r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_58 ),
    inference(avatar_component_clause,[],[f3194])).

fof(f3194,plain,
    ( spl9_58
  <=> r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_58])])).

fof(f4211,plain,
    ( ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | ~ spl9_50
    | spl9_72 ),
    inference(subsumption_resolution,[],[f4193,f2166])).

fof(f2166,plain,
    ( r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl9_50 ),
    inference(avatar_component_clause,[],[f2165])).

fof(f2165,plain,
    ( spl9_50
  <=> r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_50])])).

fof(f4193,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | spl9_72 ),
    inference(superposition,[],[f4149,f266])).

fof(f266,plain,
    ( ! [X14] :
        ( k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X14)) = X14
        | ~ r2_hidden(X14,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f108,f157])).

fof(f157,plain,
    ( v2_funct_1(sK2)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl9_11
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f108,plain,
    ( ! [X14] :
        ( ~ v2_funct_1(sK2)
        | ~ r2_hidden(X14,k2_relat_1(sK2))
        | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X14)) = X14 )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f94,f67])).

fof(f67,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f94,plain,
    ( ! [X14] :
        ( ~ v1_relat_1(sK2)
        | ~ v2_funct_1(sK2)
        | ~ r2_hidden(X14,k2_relat_1(sK2))
        | k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),X14)) = X14 )
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_funct_1)).

fof(f72,plain,
    ( v1_funct_1(sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl9_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f4149,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | spl9_72 ),
    inference(avatar_component_clause,[],[f4147])).

fof(f4147,plain,
    ( spl9_72
  <=> r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f4150,plain,
    ( ~ spl9_72
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | ~ spl9_57
    | spl9_71 ),
    inference(avatar_split_clause,[],[f4118,f4060,f3190,f156,f70,f65,f4147])).

fof(f3190,plain,
    ( spl9_57
  <=> r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_57])])).

fof(f4060,plain,
    ( spl9_71
  <=> r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_71])])).

fof(f4118,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | ~ spl9_57
    | spl9_71 ),
    inference(subsumption_resolution,[],[f4109,f3191])).

fof(f3191,plain,
    ( r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_57 ),
    inference(avatar_component_clause,[],[f3190])).

fof(f4109,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | spl9_71 ),
    inference(superposition,[],[f4062,f266])).

fof(f4062,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | spl9_71 ),
    inference(avatar_component_clause,[],[f4060])).

fof(f4063,plain,
    ( ~ spl9_71
    | ~ spl9_12
    | ~ spl9_66
    | ~ spl9_68
    | spl9_70 ),
    inference(avatar_split_clause,[],[f3984,f3973,f3945,f3879,f189,f4060])).

fof(f189,plain,
    ( spl9_12
  <=> k1_relat_1(sK2) = k3_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f3879,plain,
    ( spl9_66
  <=> r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_66])])).

fof(f3945,plain,
    ( spl9_68
  <=> r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f3973,plain,
    ( spl9_70
  <=> sP5(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f3984,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ spl9_12
    | ~ spl9_66
    | ~ spl9_68
    | spl9_70 ),
    inference(subsumption_resolution,[],[f3983,f3880])).

fof(f3880,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
    | ~ spl9_66 ),
    inference(avatar_component_clause,[],[f3879])).

fof(f3983,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ spl9_12
    | ~ spl9_68
    | spl9_70 ),
    inference(forward_demodulation,[],[f3982,f191])).

fof(f191,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f189])).

fof(f3982,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
    | ~ spl9_12
    | ~ spl9_68
    | spl9_70 ),
    inference(subsumption_resolution,[],[f3981,f3946])).

fof(f3946,plain,
    ( r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f3945])).

fof(f3981,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
    | ~ spl9_12
    | spl9_70 ),
    inference(forward_demodulation,[],[f3978,f191])).

fof(f3978,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
    | ~ r2_hidden(k4_tarski(k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2)))),k1_funct_1(sK2,k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))))),sK1)
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k3_relat_1(sK0))
    | spl9_70 ),
    inference(resolution,[],[f3975,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP5(X4,X3,X2,X1,X0)
      | ~ r2_hidden(X4,k3_relat_1(X0))
      | ~ r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
      | ~ r2_hidden(X3,k3_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) )
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
              <=> ( ! [X3,X4] :
                      ( r2_hidden(k4_tarski(X3,X4),X0)
                    <=> ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
                        & r2_hidden(X4,k3_relat_1(X0))
                        & r2_hidden(X3,k3_relat_1(X0)) ) )
                  & v2_funct_1(X2)
                  & k2_relat_1(X2) = k3_relat_1(X1)
                  & k1_relat_1(X2) = k3_relat_1(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_wellord1)).

fof(f3975,plain,
    ( ~ sP5(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),sK2,sK1,sK0)
    | spl9_70 ),
    inference(avatar_component_clause,[],[f3973])).

fof(f3976,plain,
    ( ~ spl9_70
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_49 ),
    inference(avatar_split_clause,[],[f3877,f2161,f113,f80,f75,f70,f65,f3973])).

fof(f75,plain,
    ( spl9_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f80,plain,
    ( spl9_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f113,plain,
    ( spl9_5
  <=> r3_wellord1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2161,plain,
    ( spl9_49
  <=> r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f3877,plain,
    ( ~ sP5(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_49 ),
    inference(subsumption_resolution,[],[f3876,f77])).

fof(f77,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f75])).

fof(f3876,plain,
    ( ~ v1_relat_1(sK1)
    | ~ sP5(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_49 ),
    inference(resolution,[],[f3866,f115])).

fof(f115,plain,
    ( r3_wellord1(sK0,sK1,sK2)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f3866,plain,
    ( ! [X2] :
        ( ~ r3_wellord1(sK0,X2,sK2)
        | ~ v1_relat_1(X2)
        | ~ sP5(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),sK2,X2,sK0) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | spl9_49 ),
    inference(subsumption_resolution,[],[f3851,f82])).

fof(f82,plain,
    ( v1_relat_1(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f3851,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(sK0)
        | ~ sP5(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),sK2,X2,sK0)
        | ~ v1_relat_1(X2)
        | ~ r3_wellord1(sK0,X2,sK2) )
    | ~ spl9_1
    | ~ spl9_2
    | spl9_49 ),
    inference(resolution,[],[f2163,f98])).

fof(f98,plain,
    ( ! [X2,X0,X3,X1] :
        ( r2_hidden(k4_tarski(X3,X2),X1)
        | ~ v1_relat_1(X1)
        | ~ sP5(X2,X3,sK2,X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r3_wellord1(X1,X0,sK2) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f84,f67])).

fof(f84,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ sP5(X2,X3,sK2,X0,X1)
        | r2_hidden(k4_tarski(X3,X2),X1)
        | ~ r3_wellord1(X1,X0,sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | ~ sP5(X4,X3,X2,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2163,plain,
    ( ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | spl9_49 ),
    inference(avatar_component_clause,[],[f2161])).

fof(f3961,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_58
    | spl9_68 ),
    inference(avatar_contradiction_clause,[],[f3960])).

fof(f3960,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_58
    | spl9_68 ),
    inference(subsumption_resolution,[],[f3952,f3195])).

fof(f3952,plain,
    ( ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_68 ),
    inference(resolution,[],[f3947,f1352])).

fof(f1352,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK2),X2),k1_relat_1(sK2))
        | ~ r2_hidden(X2,k2_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19 ),
    inference(resolution,[],[f1346,f411])).

fof(f411,plain,
    ( ! [X16] :
        ( sP7(X16,k2_funct_1(k2_funct_1(sK2)))
        | ~ r2_hidden(X16,k2_relat_1(sK2)) )
    | ~ spl9_8
    | ~ spl9_15
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f410,f314])).

fof(f314,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl9_19
  <=> k2_relat_1(sK2) = k2_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f410,plain,
    ( ! [X16] :
        ( sP7(X16,k2_funct_1(k2_funct_1(sK2)))
        | ~ r2_hidden(X16,k2_relat_1(k2_funct_1(k2_funct_1(sK2)))) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f183,f225])).

fof(f225,plain,
    ( v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f224])).

fof(f224,plain,
    ( spl9_15
  <=> v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f183,plain,
    ( ! [X16] :
        ( ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
        | sP7(X16,k2_funct_1(k2_funct_1(sK2)))
        | ~ r2_hidden(X16,k2_relat_1(k2_funct_1(k2_funct_1(sK2)))) )
    | ~ spl9_8 ),
    inference(resolution,[],[f145,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | sP7(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP7(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
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

fof(f145,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl9_8
  <=> v1_funct_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f1346,plain,
    ( ! [X10] :
        ( ~ sP7(X10,k2_funct_1(k2_funct_1(sK2)))
        | r2_hidden(k1_funct_1(k2_funct_1(sK2),X10),k1_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f1345,f301])).

fof(f301,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(k2_funct_1(k2_funct_1(sK2)),X0),k1_relat_1(sK2))
        | ~ sP7(X0,k2_funct_1(k2_funct_1(sK2))) )
    | ~ spl9_18 ),
    inference(superposition,[],[f51,f291])).

fof(f291,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl9_18
  <=> k1_relat_1(sK2) = k1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK8(X0,X2),k1_relat_1(X0))
      | ~ sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1345,plain,
    ( ! [X10] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK2),X10),k1_relat_1(sK2))
        | ~ sP7(X10,k2_funct_1(k2_funct_1(sK2)))
        | ~ r2_hidden(sK8(k2_funct_1(k2_funct_1(sK2)),X10),k1_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19 ),
    inference(subsumption_resolution,[],[f1339,f415])).

fof(f415,plain,
    ( ! [X17] :
        ( r2_hidden(X17,k2_relat_1(sK2))
        | ~ sP7(X17,k2_funct_1(k2_funct_1(sK2))) )
    | ~ spl9_8
    | ~ spl9_15
    | ~ spl9_19 ),
    inference(forward_demodulation,[],[f414,f314])).

fof(f414,plain,
    ( ! [X17] :
        ( ~ sP7(X17,k2_funct_1(k2_funct_1(sK2)))
        | r2_hidden(X17,k2_relat_1(k2_funct_1(k2_funct_1(sK2)))) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(subsumption_resolution,[],[f184,f225])).

fof(f184,plain,
    ( ! [X17] :
        ( ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
        | ~ sP7(X17,k2_funct_1(k2_funct_1(sK2)))
        | r2_hidden(X17,k2_relat_1(k2_funct_1(k2_funct_1(sK2)))) )
    | ~ spl9_8 ),
    inference(resolution,[],[f145,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ sP7(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1339,plain,
    ( ! [X10] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK2),X10),k1_relat_1(sK2))
        | ~ sP7(X10,k2_funct_1(k2_funct_1(sK2)))
        | ~ r2_hidden(sK8(k2_funct_1(k2_funct_1(sK2)),X10),k1_relat_1(sK2))
        | ~ r2_hidden(X10,k2_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19 ),
    inference(superposition,[],[f301,f504])).

fof(f504,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK2),X0) = sK8(k2_funct_1(k2_funct_1(sK2)),X0)
        | ~ r2_hidden(sK8(k2_funct_1(k2_funct_1(sK2)),X0),k1_relat_1(sK2))
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_19 ),
    inference(superposition,[],[f365,f413])).

fof(f413,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(k2_funct_1(sK2)),sK8(k2_funct_1(k2_funct_1(sK2)),X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_8
    | ~ spl9_15
    | ~ spl9_19 ),
    inference(resolution,[],[f411,f52])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | k1_funct_1(X0,sK8(X0,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f365,plain,
    ( ! [X14] :
        ( k1_funct_1(k2_funct_1(sK2),k1_funct_1(k2_funct_1(k2_funct_1(sK2)),X14)) = X14
        | ~ r2_hidden(X14,k1_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f364,f250])).

fof(f250,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl9_16
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f364,plain,
    ( ! [X14] :
        ( ~ r2_hidden(X14,k2_relat_1(k2_funct_1(sK2)))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(k2_funct_1(k2_funct_1(sK2)),X14)) = X14 )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f363,f286])).

fof(f286,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl9_17
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f363,plain,
    ( ! [X14] :
        ( ~ v2_funct_1(k2_funct_1(sK2))
        | ~ r2_hidden(X14,k2_relat_1(k2_funct_1(sK2)))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(k2_funct_1(k2_funct_1(sK2)),X14)) = X14 )
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f137,f148])).

fof(f148,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl9_9
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f137,plain,
    ( ! [X14] :
        ( ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ r2_hidden(X14,k2_relat_1(k2_funct_1(sK2)))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(k2_funct_1(k2_funct_1(sK2)),X14)) = X14 )
    | ~ spl9_7 ),
    inference(resolution,[],[f125,f57])).

fof(f125,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl9_7
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f3947,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
    | spl9_68 ),
    inference(avatar_component_clause,[],[f3945])).

fof(f3895,plain,
    ( ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_57
    | spl9_66 ),
    inference(avatar_contradiction_clause,[],[f3894])).

fof(f3894,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | ~ spl9_57
    | spl9_66 ),
    inference(subsumption_resolution,[],[f3886,f3191])).

fof(f3886,plain,
    ( ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_7
    | ~ spl9_8
    | ~ spl9_9
    | ~ spl9_15
    | ~ spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_19
    | spl9_66 ),
    inference(resolution,[],[f3881,f1352])).

fof(f3881,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_relat_1(sK2))
    | spl9_66 ),
    inference(avatar_component_clause,[],[f3879])).

fof(f3843,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_58
    | ~ spl9_64
    | spl9_65 ),
    inference(avatar_contradiction_clause,[],[f3842])).

fof(f3842,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_58
    | ~ spl9_64
    | spl9_65 ),
    inference(subsumption_resolution,[],[f3781,f3797])).

fof(f3797,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | spl9_65 ),
    inference(avatar_component_clause,[],[f3795])).

fof(f3795,plain,
    ( spl9_65
  <=> r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_65])])).

fof(f3781,plain,
    ( r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_58
    | ~ spl9_64 ),
    inference(subsumption_resolution,[],[f3780,f3195])).

fof(f3780,plain,
    ( r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_64 ),
    inference(superposition,[],[f3702,f994])).

fof(f994,plain,
    ( ! [X0] :
        ( sK8(sK2,X0) = k1_funct_1(k2_funct_1(sK2),X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f987,f110])).

fof(f110,plain,
    ( ! [X16] :
        ( sP7(X16,sK2)
        | ~ r2_hidden(X16,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f96,f67])).

fof(f96,plain,
    ( ! [X16] :
        ( ~ v1_relat_1(sK2)
        | sP7(X16,sK2)
        | ~ r2_hidden(X16,k2_relat_1(sK2)) )
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f61])).

fof(f987,plain,
    ( ! [X0] :
        ( sK8(sK2,X0) = k1_funct_1(k2_funct_1(sK2),X0)
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ sP7(X0,sK2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(resolution,[],[f904,f51])).

fof(f904,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK8(sK2,X1),k1_relat_1(sK2))
        | k1_funct_1(k2_funct_1(sK2),X1) = sK8(sK2,X1)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(superposition,[],[f900,f141])).

fof(f141,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK8(sK2,X0)) = X0
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f110,f52])).

fof(f900,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f891,f275])).

fof(f275,plain,
    ( ! [X16] :
        ( sP7(X16,k2_funct_1(sK2))
        | ~ r2_hidden(X16,k1_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f274,f250])).

fof(f274,plain,
    ( ! [X16] :
        ( sP7(X16,k2_funct_1(sK2))
        | ~ r2_hidden(X16,k2_relat_1(k2_funct_1(sK2))) )
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f139,f148])).

fof(f139,plain,
    ( ! [X16] :
        ( ~ v1_relat_1(k2_funct_1(sK2))
        | sP7(X16,k2_funct_1(sK2))
        | ~ r2_hidden(X16,k2_relat_1(k2_funct_1(sK2))) )
    | ~ spl9_7 ),
    inference(resolution,[],[f125,f61])).

fof(f891,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0
        | ~ sP7(X0,k2_funct_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(resolution,[],[f803,f239])).

fof(f239,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(k2_funct_1(sK2),X0),k2_relat_1(sK2))
        | ~ sP7(X0,k2_funct_1(sK2)) )
    | ~ spl9_10 ),
    inference(superposition,[],[f51,f154])).

fof(f154,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl9_10
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f803,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK8(k2_funct_1(sK2),X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0 )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(duplicate_literal_removal,[],[f800])).

fof(f800,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK2),k1_funct_1(sK2,X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2))
        | ~ r2_hidden(sK8(k2_funct_1(sK2),X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(superposition,[],[f276,f419])).

fof(f419,plain,
    ( ! [X0] :
        ( sK8(k2_funct_1(sK2),X0) = k1_funct_1(sK2,X0)
        | ~ r2_hidden(sK8(k2_funct_1(sK2),X0),k2_relat_1(sK2))
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(superposition,[],[f266,f276])).

fof(f276,plain,
    ( ! [X0] :
        ( k1_funct_1(k2_funct_1(sK2),sK8(k2_funct_1(sK2),X0)) = X0
        | ~ r2_hidden(X0,k1_relat_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(resolution,[],[f275,f52])).

fof(f3702,plain,
    ( r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_64 ),
    inference(avatar_component_clause,[],[f3700])).

fof(f3700,plain,
    ( spl9_64
  <=> r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_64])])).

fof(f3798,plain,
    ( ~ spl9_65
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_50
    | ~ spl9_57
    | ~ spl9_58 ),
    inference(avatar_split_clause,[],[f3761,f3194,f3190,f2165,f113,f80,f75,f70,f65,f3795])).

fof(f3761,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_50
    | ~ spl9_57
    | ~ spl9_58 ),
    inference(subsumption_resolution,[],[f3760,f3195])).

fof(f3760,plain,
    ( ~ r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_50
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f3747,f3191])).

fof(f3747,plain,
    ( ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),sK8(sK2,sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_50 ),
    inference(resolution,[],[f2167,f1402])).

fof(f1402,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X1,X0),sK1)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(sK8(sK2,X1),sK8(sK2,X0)),sK0)
        | ~ r2_hidden(X0,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f1401,f77])).

fof(f1401,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(sK8(sK2,X1),sK8(sK2,X0)),sK0)
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f1400,f82])).

fof(f1400,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(sK1)
        | ~ r2_hidden(k4_tarski(sK8(sK2,X1),sK8(sK2,X0)),sK0)
        | r2_hidden(k4_tarski(X1,X0),sK1) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f815,f115])).

fof(f815,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r3_wellord1(X3,X2,sK2)
        | ~ r2_hidden(X1,k2_relat_1(sK2))
        | ~ r2_hidden(X0,k2_relat_1(sK2))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(sK8(sK2,X0),sK8(sK2,X1)),X3)
        | r2_hidden(k4_tarski(X0,X1),X2) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f503,f99])).

fof(f99,plain,
    ( ! [X6,X4,X7,X5] :
        ( sP5(X6,X7,sK2,X4,X5)
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X4)
        | ~ r2_hidden(k4_tarski(X7,X6),X5)
        | ~ r3_wellord1(X5,X4,sK2) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f85,f67])).

fof(f85,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v1_relat_1(X4)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X5)
        | sP5(X6,X7,sK2,X4,X5)
        | ~ r2_hidden(k4_tarski(X7,X6),X5)
        | ~ r3_wellord1(X5,X4,sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | sP5(X4,X3,X2,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f503,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ sP5(sK8(sK2,X5),sK8(sK2,X4),sK2,X6,X7)
        | r2_hidden(k4_tarski(X4,X5),X6)
        | ~ r2_hidden(X5,k2_relat_1(sK2))
        | ~ r2_hidden(X4,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(superposition,[],[f280,f141])).

fof(f280,plain,
    ( ! [X4,X2,X3,X1] :
        ( r2_hidden(k4_tarski(k1_funct_1(sK2,X2),X1),X3)
        | ~ sP5(sK8(sK2,X1),X2,sK2,X3,X4)
        | ~ r2_hidden(X1,k2_relat_1(sK2)) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(superposition,[],[f35,f141])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(k1_funct_1(X2,X3),k1_funct_1(X2,X4)),X1)
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2167,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | spl9_50 ),
    inference(avatar_component_clause,[],[f2165])).

fof(f3703,plain,
    ( spl9_64
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_49
    | ~ spl9_57 ),
    inference(avatar_split_clause,[],[f3460,f3190,f2161,f248,f156,f152,f147,f123,f70,f65,f3700])).

fof(f3460,plain,
    ( r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_49
    | ~ spl9_57 ),
    inference(subsumption_resolution,[],[f3458,f3191])).

fof(f3458,plain,
    ( r2_hidden(k4_tarski(sK8(sK2,sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_11
    | ~ spl9_16
    | ~ spl9_49 ),
    inference(superposition,[],[f2162,f994])).

fof(f2162,plain,
    ( r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f2161])).

fof(f3491,plain,
    ( ~ spl9_13
    | ~ spl9_51
    | spl9_58 ),
    inference(avatar_contradiction_clause,[],[f3488])).

fof(f3488,plain,
    ( $false
    | ~ spl9_13
    | ~ spl9_51
    | spl9_58 ),
    inference(resolution,[],[f3210,f2222])).

fof(f2222,plain,
    ( sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | ~ spl9_51 ),
    inference(avatar_component_clause,[],[f2220])).

fof(f2220,plain,
    ( spl9_51
  <=> sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_51])])).

fof(f3210,plain,
    ( ! [X4,X2,X3] : ~ sP5(sK4(sK1,sK0,k2_funct_1(sK2)),X2,X3,X4,sK1)
    | ~ spl9_13
    | spl9_58 ),
    inference(resolution,[],[f3196,f212])).

fof(f212,plain,
    ( ! [X10,X8,X11,X9] :
        ( r2_hidden(X8,k2_relat_1(sK2))
        | ~ sP5(X8,X9,X10,X11,sK1) )
    | ~ spl9_13 ),
    inference(superposition,[],[f34,f207])).

fof(f207,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f205,plain,
    ( spl9_13
  <=> k2_relat_1(sK2) = k3_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X4,k3_relat_1(X0))
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3196,plain,
    ( ~ r2_hidden(sK4(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | spl9_58 ),
    inference(avatar_component_clause,[],[f3194])).

fof(f3449,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_51
    | spl9_58 ),
    inference(avatar_contradiction_clause,[],[f3448])).

fof(f3448,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_51
    | spl9_58 ),
    inference(subsumption_resolution,[],[f3447,f120])).

fof(f120,plain,
    ( ~ r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | spl9_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl9_6
  <=> r3_wellord1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f3447,plain,
    ( r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_51
    | spl9_58 ),
    inference(subsumption_resolution,[],[f3446,f191])).

fof(f3446,plain,
    ( k1_relat_1(sK2) != k3_relat_1(sK0)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_51
    | spl9_58 ),
    inference(subsumption_resolution,[],[f3445,f2221])).

fof(f2221,plain,
    ( ~ sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | spl9_51 ),
    inference(avatar_component_clause,[],[f2220])).

fof(f3445,plain,
    ( sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k1_relat_1(sK2) != k3_relat_1(sK0)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_58 ),
    inference(subsumption_resolution,[],[f3444,f77])).

fof(f3444,plain,
    ( ~ v1_relat_1(sK1)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k1_relat_1(sK2) != k3_relat_1(sK0)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_58 ),
    inference(subsumption_resolution,[],[f3443,f82])).

fof(f3443,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k1_relat_1(sK2) != k3_relat_1(sK0)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_58 ),
    inference(subsumption_resolution,[],[f3416,f207])).

fof(f3416,plain,
    ( k2_relat_1(sK2) != k3_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k1_relat_1(sK2) != k3_relat_1(sK0)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_58 ),
    inference(resolution,[],[f3208,f434])).

fof(f434,plain,
    ( ! [X2,X1] :
        ( r2_hidden(k4_tarski(sK3(X1,X2,k2_funct_1(sK2)),sK4(X1,X2,k2_funct_1(sK2))),X1)
        | k3_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | sP5(sK4(X1,X2,k2_funct_1(sK2)),sK3(X1,X2,k2_funct_1(sK2)),k2_funct_1(sK2),X2,X1)
        | k3_relat_1(X2) != k1_relat_1(sK2)
        | r3_wellord1(X1,X2,k2_funct_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f433,f250])).

fof(f433,plain,
    ( ! [X2,X1] :
        ( k3_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | k3_relat_1(X2) != k2_relat_1(k2_funct_1(sK2))
        | sP5(sK4(X1,X2,k2_funct_1(sK2)),sK3(X1,X2,k2_funct_1(sK2)),k2_funct_1(sK2),X2,X1)
        | r2_hidden(k4_tarski(sK3(X1,X2,k2_funct_1(sK2)),sK4(X1,X2,k2_funct_1(sK2))),X1)
        | r3_wellord1(X1,X2,k2_funct_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f243,f286])).

fof(f243,plain,
    ( ! [X2,X1] :
        ( k3_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1)
        | k3_relat_1(X2) != k2_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | sP5(sK4(X1,X2,k2_funct_1(sK2)),sK3(X1,X2,k2_funct_1(sK2)),k2_funct_1(sK2),X2,X1)
        | r2_hidden(k4_tarski(sK3(X1,X2,k2_funct_1(sK2)),sK4(X1,X2,k2_funct_1(sK2))),X1)
        | r3_wellord1(X1,X2,k2_funct_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f242,f125])).

fof(f242,plain,
    ( ! [X2,X1] :
        ( k3_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X1)
        | k3_relat_1(X2) != k2_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | sP5(sK4(X1,X2,k2_funct_1(sK2)),sK3(X1,X2,k2_funct_1(sK2)),k2_funct_1(sK2),X2,X1)
        | r2_hidden(k4_tarski(sK3(X1,X2,k2_funct_1(sK2)),sK4(X1,X2,k2_funct_1(sK2))),X1)
        | r3_wellord1(X1,X2,k2_funct_1(sK2)) )
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f240,f148])).

fof(f240,plain,
    ( ! [X2,X1] :
        ( k3_relat_1(X1) != k2_relat_1(sK2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X1)
        | k3_relat_1(X2) != k2_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | sP5(sK4(X1,X2,k2_funct_1(sK2)),sK3(X1,X2,k2_funct_1(sK2)),k2_funct_1(sK2),X2,X1)
        | r2_hidden(k4_tarski(sK3(X1,X2,k2_funct_1(sK2)),sK4(X1,X2,k2_funct_1(sK2))),X1)
        | r3_wellord1(X1,X2,k2_funct_1(sK2)) )
    | ~ spl9_10 ),
    inference(superposition,[],[f36,f154])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v2_funct_1(X2)
      | sP5(sK4(X0,X1,X2),sK3(X0,X1,X2),X2,X1,X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3208,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(X0,sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ spl9_3
    | ~ spl9_13
    | spl9_58 ),
    inference(resolution,[],[f3196,f216])).

fof(f216,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X3,X2),sK1) )
    | ~ spl9_3
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f210,f77])).

fof(f210,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k2_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X3,X2),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_13 ),
    inference(superposition,[],[f60,f207])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f3382,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_57 ),
    inference(avatar_contradiction_clause,[],[f3381])).

fof(f3381,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3380,f250])).

fof(f3380,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | spl9_57 ),
    inference(forward_demodulation,[],[f3379,f191])).

fof(f3379,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_17
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3378,f120])).

fof(f3378,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_17
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3377,f154])).

fof(f3377,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_17
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3376,f3205])).

fof(f3205,plain,
    ( ! [X6,X7,X5] : ~ sP5(X5,sK3(sK1,sK0,k2_funct_1(sK2)),X6,X7,sK1)
    | ~ spl9_13
    | spl9_57 ),
    inference(resolution,[],[f3192,f211])).

fof(f211,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(X4,k2_relat_1(sK2))
        | ~ sP5(X5,X4,X6,X7,sK1) )
    | ~ spl9_13 ),
    inference(superposition,[],[f33,f207])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ sP5(X4,X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3192,plain,
    ( ~ r2_hidden(sK3(sK1,sK0,k2_funct_1(sK2)),k2_relat_1(sK2))
    | spl9_57 ),
    inference(avatar_component_clause,[],[f3190])).

fof(f3376,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_17
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3375,f286])).

fof(f3375,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_13
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3374,f125])).

fof(f3374,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_13
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3373,f148])).

fof(f3373,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_13
    | spl9_57 ),
    inference(subsumption_resolution,[],[f3299,f82])).

fof(f3299,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_13
    | spl9_57 ),
    inference(resolution,[],[f3203,f217])).

fof(f217,plain,
    ( ! [X12,X13] :
        ( r2_hidden(k4_tarski(sK3(sK1,X13,X12),sK4(sK1,X13,X12)),sK1)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | k2_relat_1(X12) != k3_relat_1(X13)
        | ~ v2_funct_1(X12)
        | sP5(sK4(sK1,X13,X12),sK3(sK1,X13,X12),X12,X13,sK1)
        | k2_relat_1(sK2) != k1_relat_1(X12)
        | r3_wellord1(sK1,X13,X12) )
    | ~ spl9_3
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f213,f77])).

fof(f213,plain,
    ( ! [X12,X13] :
        ( k2_relat_1(sK2) != k1_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ v1_relat_1(X12)
        | ~ v1_funct_1(X12)
        | ~ v1_relat_1(sK1)
        | k2_relat_1(X12) != k3_relat_1(X13)
        | ~ v2_funct_1(X12)
        | sP5(sK4(sK1,X13,X12),sK3(sK1,X13,X12),X12,X13,sK1)
        | r2_hidden(k4_tarski(sK3(sK1,X13,X12),sK4(sK1,X13,X12)),sK1)
        | r3_wellord1(sK1,X13,X12) )
    | ~ spl9_13 ),
    inference(superposition,[],[f36,f207])).

fof(f3203,plain,
    ( ! [X1] : ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),X1),sK1)
    | ~ spl9_3
    | ~ spl9_13
    | spl9_57 ),
    inference(resolution,[],[f3192,f215])).

fof(f215,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl9_3
    | ~ spl9_13 ),
    inference(subsumption_resolution,[],[f209,f77])).

fof(f209,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k2_relat_1(sK2))
        | ~ r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_13 ),
    inference(superposition,[],[f59,f207])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2216,plain,
    ( ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_49
    | spl9_50 ),
    inference(avatar_contradiction_clause,[],[f2215])).

fof(f2215,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_49
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2188,f2207])).

fof(f2207,plain,
    ( ! [X11] : ~ sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,X11)
    | spl9_49 ),
    inference(resolution,[],[f2163,f35])).

fof(f2188,plain,
    ( sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2187,f250])).

fof(f2187,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_17
    | spl9_50 ),
    inference(forward_demodulation,[],[f2186,f191])).

fof(f2186,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_17
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2185,f120])).

fof(f2185,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_13
    | ~ spl9_17
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2184,f154])).

fof(f2184,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_13
    | ~ spl9_17
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2183,f286])).

fof(f2183,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_13
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2182,f125])).

fof(f2182,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_9
    | ~ spl9_13
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2181,f148])).

fof(f2181,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_13
    | spl9_50 ),
    inference(subsumption_resolution,[],[f2169,f82])).

fof(f2169,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(sK0)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | sP5(sK4(sK1,sK0,k2_funct_1(sK2)),sK3(sK1,sK0,k2_funct_1(sK2)),k2_funct_1(sK2),sK0,sK1)
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl9_3
    | ~ spl9_13
    | spl9_50 ),
    inference(resolution,[],[f2167,f217])).

fof(f2168,plain,
    ( ~ spl9_49
    | ~ spl9_50
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f1222,f285,f248,f205,f189,f152,f147,f123,f118,f80,f75,f2165,f2161])).

fof(f1222,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_3
    | ~ spl9_4
    | spl9_6
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1221,f120])).

fof(f1221,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f1219,f77])).

fof(f1219,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(trivial_inequality_removal,[],[f1218])).

fof(f1218,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(k4_tarski(sK3(sK1,sK0,k2_funct_1(sK2)),sK4(sK1,sK0,k2_funct_1(sK2))),sK1)
    | r3_wellord1(sK1,sK0,k2_funct_1(sK2))
    | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(sK1,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(sK1,sK0,k2_funct_1(sK2)))),sK0)
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(superposition,[],[f686,f207])).

fof(f686,plain,
    ( ! [X0] :
        ( k3_relat_1(X0) != k2_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(k4_tarski(sK3(X0,sK0,k2_funct_1(sK2)),sK4(X0,sK0,k2_funct_1(sK2))),X0)
        | r3_wellord1(X0,sK0,k2_funct_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(X0,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(X0,sK0,k2_funct_1(sK2)))),sK0) )
    | ~ spl9_4
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f685,f82])).

fof(f685,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | k3_relat_1(X0) != k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK3(X0,sK0,k2_funct_1(sK2)),sK4(X0,sK0,k2_funct_1(sK2))),X0)
        | r3_wellord1(X0,sK0,k2_funct_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(X0,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(X0,sK0,k2_funct_1(sK2)))),sK0) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(trivial_inequality_removal,[],[f683])).

fof(f683,plain,
    ( ! [X0] :
        ( k1_relat_1(sK2) != k1_relat_1(sK2)
        | ~ v1_relat_1(sK0)
        | ~ v1_relat_1(X0)
        | k3_relat_1(X0) != k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK3(X0,sK0,k2_funct_1(sK2)),sK4(X0,sK0,k2_funct_1(sK2))),X0)
        | r3_wellord1(X0,sK0,k2_funct_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(X0,sK0,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(X0,sK0,k2_funct_1(sK2)))),sK0) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_12
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(superposition,[],[f446,f191])).

fof(f446,plain,
    ( ! [X0,X1] :
        ( k3_relat_1(X1) != k1_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k3_relat_1(X0) != k2_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK3(X0,X1,k2_funct_1(sK2)),sK4(X0,X1,k2_funct_1(sK2))),X0)
        | r3_wellord1(X0,X1,k2_funct_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(X0,X1,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(X0,X1,k2_funct_1(sK2)))),X1) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f445,f59])).

fof(f445,plain,
    ( ! [X0,X1] :
        ( k3_relat_1(X0) != k2_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k3_relat_1(X1) != k1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK3(X0,X1,k2_funct_1(sK2)),sK4(X0,X1,k2_funct_1(sK2))),X0)
        | r3_wellord1(X0,X1,k2_funct_1(sK2))
        | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(X0,X1,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(X0,X1,k2_funct_1(sK2)))),X1)
        | ~ r2_hidden(sK3(X0,X1,k2_funct_1(sK2)),k3_relat_1(X0)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f444,f60])).

fof(f444,plain,
    ( ! [X0,X1] :
        ( k3_relat_1(X0) != k2_relat_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0)
        | k3_relat_1(X1) != k1_relat_1(sK2)
        | ~ r2_hidden(k4_tarski(sK3(X0,X1,k2_funct_1(sK2)),sK4(X0,X1,k2_funct_1(sK2))),X0)
        | r3_wellord1(X0,X1,k2_funct_1(sK2))
        | ~ r2_hidden(sK4(X0,X1,k2_funct_1(sK2)),k3_relat_1(X0))
        | ~ r2_hidden(k4_tarski(k1_funct_1(k2_funct_1(sK2),sK3(X0,X1,k2_funct_1(sK2))),k1_funct_1(k2_funct_1(sK2),sK4(X0,X1,k2_funct_1(sK2)))),X1)
        | ~ r2_hidden(sK3(X0,X1,k2_funct_1(sK2)),k3_relat_1(X0)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(resolution,[],[f443,f32])).

fof(f443,plain,
    ( ! [X4,X3] :
        ( ~ sP5(sK4(X3,X4,k2_funct_1(sK2)),sK3(X3,X4,k2_funct_1(sK2)),k2_funct_1(sK2),X4,X3)
        | k2_relat_1(sK2) != k3_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X3)
        | k1_relat_1(sK2) != k3_relat_1(X4)
        | ~ r2_hidden(k4_tarski(sK3(X3,X4,k2_funct_1(sK2)),sK4(X3,X4,k2_funct_1(sK2))),X3)
        | r3_wellord1(X3,X4,k2_funct_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_16
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f442,f250])).

fof(f442,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK2) != k3_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X3)
        | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(X4)
        | ~ sP5(sK4(X3,X4,k2_funct_1(sK2)),sK3(X3,X4,k2_funct_1(sK2)),k2_funct_1(sK2),X4,X3)
        | ~ r2_hidden(k4_tarski(sK3(X3,X4,k2_funct_1(sK2)),sK4(X3,X4,k2_funct_1(sK2))),X3)
        | r3_wellord1(X3,X4,k2_funct_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f245,f286])).

fof(f245,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK2) != k3_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X3)
        | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(X4)
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ sP5(sK4(X3,X4,k2_funct_1(sK2)),sK3(X3,X4,k2_funct_1(sK2)),k2_funct_1(sK2),X4,X3)
        | ~ r2_hidden(k4_tarski(sK3(X3,X4,k2_funct_1(sK2)),sK4(X3,X4,k2_funct_1(sK2))),X3)
        | r3_wellord1(X3,X4,k2_funct_1(sK2)) )
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f244,f125])).

fof(f244,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK2) != k3_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X3)
        | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(X4)
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ sP5(sK4(X3,X4,k2_funct_1(sK2)),sK3(X3,X4,k2_funct_1(sK2)),k2_funct_1(sK2),X4,X3)
        | ~ r2_hidden(k4_tarski(sK3(X3,X4,k2_funct_1(sK2)),sK4(X3,X4,k2_funct_1(sK2))),X3)
        | r3_wellord1(X3,X4,k2_funct_1(sK2)) )
    | ~ spl9_9
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f241,f148])).

fof(f241,plain,
    ( ! [X4,X3] :
        ( k2_relat_1(sK2) != k3_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(X3)
        | k2_relat_1(k2_funct_1(sK2)) != k3_relat_1(X4)
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ sP5(sK4(X3,X4,k2_funct_1(sK2)),sK3(X3,X4,k2_funct_1(sK2)),k2_funct_1(sK2),X4,X3)
        | ~ r2_hidden(k4_tarski(sK3(X3,X4,k2_funct_1(sK2)),sK4(X3,X4,k2_funct_1(sK2))),X3)
        | r3_wellord1(X3,X4,k2_funct_1(sK2)) )
    | ~ spl9_10 ),
    inference(superposition,[],[f37,f154])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) != k3_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X2) != k3_relat_1(X1)
      | ~ v2_funct_1(X2)
      | ~ sP5(sK4(X0,X1,X2),sK3(X0,X1,X2),X2,X1,X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f315,plain,
    ( spl9_19
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f310,f285,f152,f147,f123,f312])).

fof(f310,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f309,f154])).

fof(f309,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f308,f286])).

fof(f308,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f134,f148])).

fof(f134,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7 ),
    inference(resolution,[],[f125,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f298,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | spl9_17 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11
    | spl9_17 ),
    inference(subsumption_resolution,[],[f296,f67])).

fof(f296,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_2
    | ~ spl9_11
    | spl9_17 ),
    inference(subsumption_resolution,[],[f295,f157])).

fof(f295,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl9_2
    | spl9_17 ),
    inference(subsumption_resolution,[],[f293,f72])).

fof(f293,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl9_17 ),
    inference(resolution,[],[f287,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f287,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl9_17 ),
    inference(avatar_component_clause,[],[f285])).

fof(f292,plain,
    ( ~ spl9_17
    | spl9_18
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f283,f248,f147,f123,f289,f285])).

fof(f283,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl9_7
    | ~ spl9_9
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f282,f250])).

fof(f282,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7
    | ~ spl9_9 ),
    inference(subsumption_resolution,[],[f133,f148])).

fof(f133,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7 ),
    inference(resolution,[],[f125,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f251,plain,
    ( spl9_16
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11 ),
    inference(avatar_split_clause,[],[f246,f156,f70,f65,f248])).

fof(f246,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_11 ),
    inference(subsumption_resolution,[],[f105,f157])).

fof(f105,plain,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f91,f67])).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f49])).

fof(f238,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5
    | spl9_11 ),
    inference(subsumption_resolution,[],[f236,f77])).

fof(f236,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5
    | spl9_11 ),
    inference(subsumption_resolution,[],[f235,f82])).

fof(f235,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5
    | spl9_11 ),
    inference(resolution,[],[f162,f115])).

fof(f162,plain,
    ( ! [X0,X1] :
        ( ~ r3_wellord1(X1,X0,sK2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl9_1
    | ~ spl9_2
    | spl9_11 ),
    inference(subsumption_resolution,[],[f161,f72])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ r3_wellord1(X1,X0,sK2) )
    | ~ spl9_1
    | spl9_11 ),
    inference(subsumption_resolution,[],[f160,f67])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(X1)
        | ~ r3_wellord1(X1,X0,sK2) )
    | spl9_11 ),
    inference(resolution,[],[f158,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f158,plain,
    ( ~ v2_funct_1(sK2)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f156])).

fof(f232,plain,
    ( ~ spl9_7
    | ~ spl9_9
    | spl9_15 ),
    inference(avatar_contradiction_clause,[],[f231])).

fof(f231,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_9
    | spl9_15 ),
    inference(subsumption_resolution,[],[f230,f148])).

fof(f230,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl9_7
    | spl9_15 ),
    inference(subsumption_resolution,[],[f228,f125])).

fof(f228,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl9_15 ),
    inference(resolution,[],[f226,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f226,plain,
    ( ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f224])).

fof(f208,plain,
    ( spl9_13
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f187,f113,f80,f75,f70,f65,f205])).

fof(f187,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f186,f77])).

fof(f186,plain,
    ( k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f185,f82])).

fof(f185,plain,
    ( ~ v1_relat_1(sK0)
    | k2_relat_1(sK2) = k3_relat_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f101,f115])).

fof(f101,plain,
    ( ! [X10,X11] :
        ( ~ r3_wellord1(X11,X10,sK2)
        | ~ v1_relat_1(X11)
        | k2_relat_1(sK2) = k3_relat_1(X10)
        | ~ v1_relat_1(X10) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f87,f67])).

fof(f87,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(X10)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X11)
        | k2_relat_1(sK2) = k3_relat_1(X10)
        | ~ r3_wellord1(X11,X10,sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X2) = k3_relat_1(X1)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f192,plain,
    ( spl9_12
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f170,f113,f80,f75,f70,f65,f189])).

fof(f170,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f169,f77])).

fof(f169,plain,
    ( k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f168,f82])).

fof(f168,plain,
    ( ~ v1_relat_1(sK0)
    | k1_relat_1(sK2) = k3_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f100,f115])).

fof(f100,plain,
    ( ! [X8,X9] :
        ( ~ r3_wellord1(X9,X8,sK2)
        | ~ v1_relat_1(X9)
        | k1_relat_1(sK2) = k3_relat_1(X9)
        | ~ v1_relat_1(X8) )
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f86,f67])).

fof(f86,plain,
    ( ! [X8,X9] :
        ( ~ v1_relat_1(X8)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X9)
        | k1_relat_1(sK2) = k3_relat_1(X9)
        | ~ r3_wellord1(X9,X8,sK2) )
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X2) = k3_relat_1(X0)
      | ~ r3_wellord1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f167,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | spl9_9 ),
    inference(subsumption_resolution,[],[f165,f67])).

fof(f165,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl9_2
    | spl9_9 ),
    inference(subsumption_resolution,[],[f163,f72])).

fof(f163,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl9_9 ),
    inference(resolution,[],[f149,f46])).

fof(f149,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f147])).

fof(f159,plain,
    ( spl9_10
    | ~ spl9_11
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f104,f70,f65,f156,f152])).

fof(f104,plain,
    ( ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f90,f67])).

fof(f90,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f48])).

fof(f150,plain,
    ( spl9_8
    | ~ spl9_9
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f132,f123,f147,f143])).

fof(f132,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ spl9_7 ),
    inference(resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f126,plain,
    ( spl9_7
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f103,f70,f65,f123])).

fof(f103,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f89,f67])).

fof(f89,plain,
    ( ~ v1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl9_2 ),
    inference(resolution,[],[f72,f47])).

fof(f121,plain,(
    ~ spl9_6 ),
    inference(avatar_split_clause,[],[f29,f118])).

fof(f29,plain,(
    ~ r3_wellord1(sK1,sK0,k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r3_wellord1(X1,X0,k2_funct_1(X2))
              & r3_wellord1(X0,X1,X2)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( r3_wellord1(X0,X1,X2)
                 => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => r3_wellord1(X1,X0,k2_funct_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_wellord1)).

fof(f116,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f28,f113])).

fof(f28,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f78,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f68,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
