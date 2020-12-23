%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t53_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:24 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 179 expanded)
%              Number of leaves         :   18 (  71 expanded)
%              Depth                    :   12
%              Number of atoms          :  312 ( 705 expanded)
%              Number of equality atoms :   27 (  85 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f59,f66,f73,f80,f87,f107,f114,f121,f238,f245,f252])).

fof(f252,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f250,f38])).

fof(f38,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t53_funct_1.p',t71_relat_1)).

fof(f250,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f249,f86])).

fof(f86,plain,
    ( k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_10
  <=> k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f249,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f248,f65])).

fof(f65,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl3_4
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f248,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f247,f72])).

fof(f72,plain,
    ( v1_funct_1(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_6
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f247,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f246,f51])).

fof(f51,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_0 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl3_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f246,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f241,f58])).

fof(f58,plain,
    ( v1_funct_1(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_2
  <=> v1_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f241,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_19 ),
    inference(resolution,[],[f237,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t53_funct_1.p',t27_funct_1)).

fof(f237,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl3_19
  <=> ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f245,plain,
    ( ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | spl3_19 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f243,f38])).

fof(f243,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f239,f86])).

fof(f239,plain,
    ( k1_relat_1(sK0) != k1_relat_1(k5_relat_1(sK0,sK1))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(unit_resulting_resolution,[],[f65,f72,f51,f58,f237,f40])).

fof(f238,plain,
    ( ~ spl3_19
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f136,f85,f78,f71,f64,f57,f50,f236])).

fof(f78,plain,
    ( spl3_9
  <=> ~ v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f136,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f135,f65])).

fof(f135,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f134,f72])).

fof(f134,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_0
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_2
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f132,f58])).

fof(f132,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f131,f79])).

fof(f79,plain,
    ( ~ v2_funct_1(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f78])).

fof(f131,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f130,f37])).

fof(f37,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t53_funct_1.p',fc4_funct_1)).

fof(f130,plain,
    ( ~ v2_funct_1(k6_relat_1(k1_relat_1(sK0)))
    | ~ r1_tarski(k2_relat_1(sK0),k1_relat_1(sK1))
    | v2_funct_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f41,f86])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
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
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t53_funct_1.p',t47_funct_1)).

fof(f121,plain,
    ( spl3_16
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f94,f64,f119])).

fof(f119,plain,
    ( spl3_16
  <=> v1_relat_1(k5_relat_1(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f94,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK1))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f65,f65,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t53_funct_1.p',dt_k5_relat_1)).

fof(f114,plain,
    ( spl3_14
    | ~ spl3_0
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f91,f64,f50,f112])).

fof(f112,plain,
    ( spl3_14
  <=> v1_relat_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f91,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ spl3_0
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f65,f51,f43])).

fof(f107,plain,
    ( spl3_12
    | ~ spl3_0 ),
    inference(avatar_split_clause,[],[f90,f50,f105])).

fof(f105,plain,
    ( spl3_12
  <=> v1_relat_1(k5_relat_1(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f90,plain,
    ( v1_relat_1(k5_relat_1(sK0,sK0))
    | ~ spl3_0 ),
    inference(unit_resulting_resolution,[],[f51,f51,f43])).

fof(f87,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ v2_funct_1(sK0)
    & k5_relat_1(sK0,sK1) = k6_relat_1(k1_relat_1(sK0))
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ~ v2_funct_1(X0)
        & ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v2_funct_1(sK0)
      & ? [X1] :
          ( k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( k5_relat_1(X0,sK1) = k6_relat_1(k1_relat_1(X0))
        & v1_funct_1(sK1)
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ~ v2_funct_1(X0)
      & ? [X1] :
          ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( ? [X1] :
              ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & v1_funct_1(X1)
              & v1_relat_1(X1) )
         => v2_funct_1(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t53_funct_1.p',t53_funct_1)).

fof(f80,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f71])).

fof(f32,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f66,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f52,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f29,f50])).

fof(f29,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
