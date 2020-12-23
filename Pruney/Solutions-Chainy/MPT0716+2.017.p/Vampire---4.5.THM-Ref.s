%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:51 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 253 expanded)
%              Number of leaves         :   28 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  375 ( 915 expanded)
%              Number of equality atoms :   43 (  64 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2164,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f70,f74,f118,f120,f129,f131,f168,f227,f230,f512,f539,f562,f564,f2032,f2162])).

fof(f2162,plain,
    ( spl3_1
    | ~ spl3_37
    | ~ spl3_99 ),
    inference(avatar_contradiction_clause,[],[f2159])).

fof(f2159,plain,
    ( $false
    | spl3_1
    | ~ spl3_37
    | ~ spl3_99 ),
    inference(resolution,[],[f2058,f71])).

fof(f71,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2058,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_37
    | ~ spl3_99 ),
    inference(superposition,[],[f511,f2031])).

fof(f2031,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_99 ),
    inference(avatar_component_clause,[],[f2030])).

fof(f2030,plain,
    ( spl3_99
  <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).

fof(f511,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl3_37
  <=> ! [X0] : r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f2032,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_99
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f2028,f104,f64,f2030,f114,f137])).

fof(f137,plain,
    ( spl3_10
  <=> v1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f114,plain,
    ( spl3_7
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f64,plain,
    ( spl3_2
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f104,plain,
    ( spl3_4
  <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2028,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f2020,f105])).

fof(f105,plain,
    ( sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f2020,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f169,f65])).

fof(f65,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK0,X0))
      | k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),X1)) ) ),
    inference(superposition,[],[f47,f89])).

fof(f89,plain,(
    ! [X8] : k2_relat_1(k7_relat_1(sK0,X8)) = k9_relat_1(sK0,X8) ),
    inference(resolution,[],[f52,f42])).

fof(f42,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <~> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) )
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
              <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                  & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1)))
            <=> ( r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1))
                & r1_tarski(X2,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

fof(f564,plain,(
    spl3_40 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | spl3_40 ),
    inference(resolution,[],[f535,f153])).

fof(f153,plain,(
    ! [X0] : v1_funct_1(k7_relat_1(sK0,X0)) ),
    inference(global_subsumption,[],[f42,f43,f44,f45,f151])).

fof(f151,plain,(
    ! [X0] :
      ( v1_funct_1(k7_relat_1(sK0,X0))
      | ~ v1_funct_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f57,f83])).

fof(f83,plain,(
    ! [X8] : k7_relat_1(sK0,X8) = k5_relat_1(k6_relat_1(X8),sK0) ),
    inference(resolution,[],[f51,f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f45,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f44,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f535,plain,
    ( ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f534])).

fof(f534,plain,
    ( spl3_40
  <=> v1_funct_1(k7_relat_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f562,plain,(
    spl3_41 ),
    inference(avatar_contradiction_clause,[],[f561])).

fof(f561,plain,
    ( $false
    | spl3_41 ),
    inference(resolution,[],[f538,f41])).

fof(f41,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f538,plain,
    ( ~ v1_funct_1(sK1)
    | spl3_41 ),
    inference(avatar_component_clause,[],[f537])).

fof(f537,plain,
    ( spl3_41
  <=> v1_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f539,plain,
    ( ~ spl3_7
    | ~ spl3_40
    | ~ spl3_10
    | ~ spl3_41
    | spl3_2
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f532,f124,f104,f64,f537,f137,f534,f114])).

fof(f124,plain,
    ( spl3_8
  <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f532,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f531,f89])).

fof(f531,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f530])).

fof(f530,plain,
    ( sK2 != sK2
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f520,f105])).

fof(f520,plain,
    ( sK2 != k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | ~ v1_funct_1(k7_relat_1(sK0,sK2))
    | ~ v1_relat_1(sK1)
    | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1))
    | ~ spl3_8 ),
    inference(superposition,[],[f48,f506])).

fof(f506,plain,
    ( sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f125,f215])).

fof(f215,plain,(
    ! [X8] : k7_relat_1(k5_relat_1(sK0,sK1),X8) = k5_relat_1(k7_relat_1(sK0,X8),sK1) ),
    inference(resolution,[],[f160,f42])).

fof(f160,plain,(
    ! [X14,X13] :
      ( ~ v1_relat_1(X13)
      | k7_relat_1(k5_relat_1(X13,sK1),X14) = k5_relat_1(k7_relat_1(X13,X14),sK1) ) ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

fof(f125,plain,
    ( sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f124])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).

fof(f512,plain,
    ( ~ spl3_9
    | spl3_37 ),
    inference(avatar_split_clause,[],[f507,f510,f127])).

fof(f127,plain,
    ( spl3_9
  <=> v1_relat_1(k5_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f507,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))
      | ~ v1_relat_1(k5_relat_1(sK0,sK1)) ) ),
    inference(superposition,[],[f50,f215])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

fof(f230,plain,
    ( spl3_4
    | ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f228,f68,f107,f104])).

fof(f107,plain,
    ( spl3_5
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( spl3_3
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f228,plain,
    ( ~ v1_relat_1(sK0)
    | sK2 = k1_relat_1(k7_relat_1(sK0,sK2))
    | ~ spl3_3 ),
    inference(resolution,[],[f69,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

fof(f69,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f227,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_3
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f226,f61,f68,f114,f107])).

fof(f226,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f200,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

fof(f200,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl3_1 ),
    inference(superposition,[],[f59,f122])).

fof(f122,plain,
    ( k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f62,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f62,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f168,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f155,f42])).

fof(f155,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_10 ),
    inference(resolution,[],[f138,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f138,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK2))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f137])).

fof(f131,plain,
    ( ~ spl3_5
    | ~ spl3_7
    | spl3_9 ),
    inference(avatar_split_clause,[],[f130,f127,f114,f107])).

fof(f130,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK0)
    | spl3_9 ),
    inference(resolution,[],[f128,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f128,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f129,plain,
    ( spl3_8
    | ~ spl3_9
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f121,f61,f127,f124])).

fof(f121,plain,
    ( ~ v1_relat_1(k5_relat_1(sK0,sK1))
    | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(resolution,[],[f62,f53])).

fof(f120,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_7 ),
    inference(resolution,[],[f115,f40])).

fof(f115,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f114])).

fof(f118,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f117])).

fof(f117,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f108,f42])).

fof(f108,plain,
    ( ~ v1_relat_1(sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f74,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f37,f68,f64,f61])).

fof(f37,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( spl3_1
    | spl3_3 ),
    inference(avatar_split_clause,[],[f38,f68,f61])).

fof(f38,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f66,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f39,f64,f61])).

fof(f39,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:46:44 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (4830)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.45  % (4833)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.45  % (4833)Refutation not found, incomplete strategy% (4833)------------------------------
% 0.22/0.45  % (4833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (4833)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.45  
% 0.22/0.45  % (4833)Memory used [KB]: 10618
% 0.22/0.45  % (4833)Time elapsed: 0.052 s
% 0.22/0.45  % (4833)------------------------------
% 0.22/0.45  % (4833)------------------------------
% 0.22/0.46  % (4841)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.46  % (4823)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.49  % (4827)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (4824)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.50  % (4825)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (4826)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (4839)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (4846)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (4826)Refutation not found, incomplete strategy% (4826)------------------------------
% 0.22/0.51  % (4826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4826)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4826)Memory used [KB]: 10618
% 0.22/0.51  % (4826)Time elapsed: 0.092 s
% 0.22/0.51  % (4826)------------------------------
% 0.22/0.51  % (4826)------------------------------
% 0.22/0.51  % (4846)Refutation not found, incomplete strategy% (4846)------------------------------
% 0.22/0.51  % (4846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (4846)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (4846)Memory used [KB]: 10618
% 0.22/0.51  % (4846)Time elapsed: 0.099 s
% 0.22/0.51  % (4846)------------------------------
% 0.22/0.51  % (4846)------------------------------
% 0.22/0.51  % (4828)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (4842)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (4843)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (4840)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.52  % (4831)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (4832)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (4834)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.53  % (4835)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.53  % (4836)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.54  % (4845)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.54  % (4837)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.54  % (4838)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.54  % (4844)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.55  % (4829)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.62/0.63  % (4835)Refutation found. Thanks to Tanya!
% 1.62/0.63  % SZS status Theorem for theBenchmark
% 1.62/0.63  % SZS output start Proof for theBenchmark
% 1.62/0.63  fof(f2164,plain,(
% 1.62/0.63    $false),
% 1.62/0.63    inference(avatar_sat_refutation,[],[f66,f70,f74,f118,f120,f129,f131,f168,f227,f230,f512,f539,f562,f564,f2032,f2162])).
% 1.62/0.63  fof(f2162,plain,(
% 1.62/0.63    spl3_1 | ~spl3_37 | ~spl3_99),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f2159])).
% 1.62/0.63  fof(f2159,plain,(
% 1.62/0.63    $false | (spl3_1 | ~spl3_37 | ~spl3_99)),
% 1.62/0.63    inference(resolution,[],[f2058,f71])).
% 1.62/0.63  fof(f71,plain,(
% 1.62/0.63    ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | spl3_1),
% 1.62/0.63    inference(avatar_component_clause,[],[f61])).
% 1.62/0.63  fof(f61,plain,(
% 1.62/0.63    spl3_1 <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.62/0.63  fof(f2058,plain,(
% 1.62/0.63    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | (~spl3_37 | ~spl3_99)),
% 1.62/0.63    inference(superposition,[],[f511,f2031])).
% 1.62/0.63  fof(f2031,plain,(
% 1.62/0.63    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_99),
% 1.62/0.63    inference(avatar_component_clause,[],[f2030])).
% 1.62/0.63  fof(f2030,plain,(
% 1.62/0.63    spl3_99 <=> sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_99])])).
% 1.62/0.63  fof(f511,plain,(
% 1.62/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))) ) | ~spl3_37),
% 1.62/0.63    inference(avatar_component_clause,[],[f510])).
% 1.62/0.63  fof(f510,plain,(
% 1.62/0.63    spl3_37 <=> ! [X0] : r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.62/0.63  fof(f2032,plain,(
% 1.62/0.63    ~spl3_10 | ~spl3_7 | spl3_99 | ~spl3_2 | ~spl3_4),
% 1.62/0.63    inference(avatar_split_clause,[],[f2028,f104,f64,f2030,f114,f137])).
% 1.62/0.63  fof(f137,plain,(
% 1.62/0.63    spl3_10 <=> v1_relat_1(k7_relat_1(sK0,sK2))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.62/0.63  fof(f114,plain,(
% 1.62/0.63    spl3_7 <=> v1_relat_1(sK1)),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.62/0.63  fof(f64,plain,(
% 1.62/0.63    spl3_2 <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.62/0.63  fof(f104,plain,(
% 1.62/0.63    spl3_4 <=> sK2 = k1_relat_1(k7_relat_1(sK0,sK2))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.62/0.63  fof(f2028,plain,(
% 1.62/0.63    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | (~spl3_2 | ~spl3_4)),
% 1.62/0.63    inference(forward_demodulation,[],[f2020,f105])).
% 1.62/0.63  fof(f105,plain,(
% 1.62/0.63    sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_4),
% 1.62/0.63    inference(avatar_component_clause,[],[f104])).
% 1.62/0.63  fof(f2020,plain,(
% 1.62/0.63    ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | k1_relat_1(k7_relat_1(sK0,sK2)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_2),
% 1.62/0.63    inference(resolution,[],[f169,f65])).
% 1.62/0.63  fof(f65,plain,(
% 1.62/0.63    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~spl3_2),
% 1.62/0.63    inference(avatar_component_clause,[],[f64])).
% 1.62/0.63  fof(f169,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~r1_tarski(k9_relat_1(sK0,X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK0,X0)) | k1_relat_1(k7_relat_1(sK0,X0)) = k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),X1))) )),
% 1.62/0.63    inference(superposition,[],[f47,f89])).
% 1.62/0.63  fof(f89,plain,(
% 1.62/0.63    ( ! [X8] : (k2_relat_1(k7_relat_1(sK0,X8)) = k9_relat_1(sK0,X8)) )),
% 1.62/0.63    inference(resolution,[],[f52,f42])).
% 1.62/0.63  fof(f42,plain,(
% 1.62/0.63    v1_relat_1(sK0)),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  fof(f18,plain,(
% 1.62/0.63    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.62/0.63    inference(flattening,[],[f17])).
% 1.62/0.63  fof(f17,plain,(
% 1.62/0.63    ? [X0] : (? [X1] : (? [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <~> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.62/0.63    inference(ennf_transformation,[],[f16])).
% 1.62/0.63  fof(f16,negated_conjecture,(
% 1.62/0.63    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.62/0.63    inference(negated_conjecture,[],[f15])).
% 1.62/0.63  fof(f15,conjecture,(
% 1.62/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : (r1_tarski(X2,k1_relat_1(k5_relat_1(X0,X1))) <=> (r1_tarski(k9_relat_1(X0,X2),k1_relat_1(X1)) & r1_tarski(X2,k1_relat_1(X0))))))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_1)).
% 1.62/0.63  fof(f52,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f27])).
% 1.62/0.63  fof(f27,plain,(
% 1.62/0.63    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f6])).
% 1.62/0.63  fof(f6,axiom,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.62/0.63  fof(f47,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f21])).
% 1.62/0.63  fof(f21,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(flattening,[],[f20])).
% 1.62/0.63  fof(f20,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : ((k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(ennf_transformation,[],[f8])).
% 1.62/0.63  fof(f8,axiom,(
% 1.62/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) => k1_relat_1(k5_relat_1(X0,X1)) = k1_relat_1(X0))))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).
% 1.62/0.63  fof(f564,plain,(
% 1.62/0.63    spl3_40),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f563])).
% 1.62/0.63  fof(f563,plain,(
% 1.62/0.63    $false | spl3_40),
% 1.62/0.63    inference(resolution,[],[f535,f153])).
% 1.62/0.63  fof(f153,plain,(
% 1.62/0.63    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0))) )),
% 1.62/0.63    inference(global_subsumption,[],[f42,f43,f44,f45,f151])).
% 1.62/0.63  fof(f151,plain,(
% 1.62/0.63    ( ! [X0] : (v1_funct_1(k7_relat_1(sK0,X0)) | ~v1_funct_1(k6_relat_1(X0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.63    inference(superposition,[],[f57,f83])).
% 1.62/0.63  fof(f83,plain,(
% 1.62/0.63    ( ! [X8] : (k7_relat_1(sK0,X8) = k5_relat_1(k6_relat_1(X8),sK0)) )),
% 1.62/0.63    inference(resolution,[],[f51,f42])).
% 1.62/0.63  fof(f51,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f26])).
% 1.62/0.63  fof(f26,plain,(
% 1.62/0.63    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f11])).
% 1.62/0.63  fof(f11,axiom,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.62/0.63  fof(f57,plain,(
% 1.62/0.63    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f33])).
% 1.62/0.63  fof(f33,plain,(
% 1.62/0.63    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(flattening,[],[f32])).
% 1.62/0.63  fof(f32,plain,(
% 1.62/0.63    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.63    inference(ennf_transformation,[],[f12])).
% 1.62/0.63  fof(f12,axiom,(
% 1.62/0.63    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 1.62/0.63  fof(f45,plain,(
% 1.62/0.63    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.62/0.63    inference(cnf_transformation,[],[f13])).
% 1.62/0.63  fof(f13,axiom,(
% 1.62/0.63    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.62/0.63  fof(f44,plain,(
% 1.62/0.63    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.62/0.63    inference(cnf_transformation,[],[f13])).
% 1.62/0.63  fof(f43,plain,(
% 1.62/0.63    v1_funct_1(sK0)),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  fof(f535,plain,(
% 1.62/0.63    ~v1_funct_1(k7_relat_1(sK0,sK2)) | spl3_40),
% 1.62/0.63    inference(avatar_component_clause,[],[f534])).
% 1.62/0.63  fof(f534,plain,(
% 1.62/0.63    spl3_40 <=> v1_funct_1(k7_relat_1(sK0,sK2))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 1.62/0.63  fof(f562,plain,(
% 1.62/0.63    spl3_41),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f561])).
% 1.62/0.63  fof(f561,plain,(
% 1.62/0.63    $false | spl3_41),
% 1.62/0.63    inference(resolution,[],[f538,f41])).
% 1.62/0.63  fof(f41,plain,(
% 1.62/0.63    v1_funct_1(sK1)),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  fof(f538,plain,(
% 1.62/0.63    ~v1_funct_1(sK1) | spl3_41),
% 1.62/0.63    inference(avatar_component_clause,[],[f537])).
% 1.62/0.63  fof(f537,plain,(
% 1.62/0.63    spl3_41 <=> v1_funct_1(sK1)),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.62/0.63  fof(f539,plain,(
% 1.62/0.63    ~spl3_7 | ~spl3_40 | ~spl3_10 | ~spl3_41 | spl3_2 | ~spl3_4 | ~spl3_8),
% 1.62/0.63    inference(avatar_split_clause,[],[f532,f124,f104,f64,f537,f137,f534,f114])).
% 1.62/0.63  fof(f124,plain,(
% 1.62/0.63    spl3_8 <=> sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.62/0.63  fof(f532,plain,(
% 1.62/0.63    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | (~spl3_4 | ~spl3_8)),
% 1.62/0.63    inference(forward_demodulation,[],[f531,f89])).
% 1.62/0.63  fof(f531,plain,(
% 1.62/0.63    ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | (~spl3_4 | ~spl3_8)),
% 1.62/0.63    inference(trivial_inequality_removal,[],[f530])).
% 1.62/0.63  fof(f530,plain,(
% 1.62/0.63    sK2 != sK2 | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | (~spl3_4 | ~spl3_8)),
% 1.62/0.63    inference(forward_demodulation,[],[f520,f105])).
% 1.62/0.63  fof(f520,plain,(
% 1.62/0.63    sK2 != k1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(sK1) | ~v1_relat_1(k7_relat_1(sK0,sK2)) | ~v1_funct_1(k7_relat_1(sK0,sK2)) | ~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK0,sK2)),k1_relat_1(sK1)) | ~spl3_8),
% 1.62/0.63    inference(superposition,[],[f48,f506])).
% 1.62/0.63  fof(f506,plain,(
% 1.62/0.63    sK2 = k1_relat_1(k5_relat_1(k7_relat_1(sK0,sK2),sK1)) | ~spl3_8),
% 1.62/0.63    inference(backward_demodulation,[],[f125,f215])).
% 1.62/0.63  fof(f215,plain,(
% 1.62/0.63    ( ! [X8] : (k7_relat_1(k5_relat_1(sK0,sK1),X8) = k5_relat_1(k7_relat_1(sK0,X8),sK1)) )),
% 1.62/0.63    inference(resolution,[],[f160,f42])).
% 1.62/0.63  fof(f160,plain,(
% 1.62/0.63    ( ! [X14,X13] : (~v1_relat_1(X13) | k7_relat_1(k5_relat_1(X13,sK1),X14) = k5_relat_1(k7_relat_1(X13,X14),sK1)) )),
% 1.62/0.63    inference(resolution,[],[f54,f40])).
% 1.62/0.63  fof(f40,plain,(
% 1.62/0.63    v1_relat_1(sK1)),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  fof(f54,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_relat_1(X1) | k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f30])).
% 1.62/0.63  fof(f30,plain,(
% 1.62/0.63    ! [X0,X1] : (! [X2] : (k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f5])).
% 1.62/0.63  fof(f5,axiom,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k7_relat_1(k5_relat_1(X1,X2),X0) = k5_relat_1(k7_relat_1(X1,X0),X2)))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).
% 1.62/0.63  fof(f125,plain,(
% 1.62/0.63    sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_8),
% 1.62/0.63    inference(avatar_component_clause,[],[f124])).
% 1.62/0.63  fof(f48,plain,(
% 1.62/0.63    ( ! [X0,X1] : (k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 1.62/0.63    inference(cnf_transformation,[],[f23])).
% 1.62/0.63  fof(f23,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(flattening,[],[f22])).
% 1.62/0.63  fof(f22,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.62/0.63    inference(ennf_transformation,[],[f14])).
% 1.62/0.63  fof(f14,axiom,(
% 1.62/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_funct_1)).
% 1.62/0.63  fof(f512,plain,(
% 1.62/0.63    ~spl3_9 | spl3_37),
% 1.62/0.63    inference(avatar_split_clause,[],[f507,f510,f127])).
% 1.62/0.63  fof(f127,plain,(
% 1.62/0.63    spl3_9 <=> v1_relat_1(k5_relat_1(sK0,sK1))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.62/0.63  fof(f507,plain,(
% 1.62/0.63    ( ! [X0] : (r1_tarski(k1_relat_1(k5_relat_1(k7_relat_1(sK0,X0),sK1)),k1_relat_1(k5_relat_1(sK0,sK1))) | ~v1_relat_1(k5_relat_1(sK0,sK1))) )),
% 1.62/0.63    inference(superposition,[],[f50,f215])).
% 1.62/0.63  fof(f50,plain,(
% 1.62/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f25])).
% 1.62/0.63  fof(f25,plain,(
% 1.62/0.63    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f9])).
% 1.62/0.63  fof(f9,axiom,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),k1_relat_1(X1)))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).
% 1.62/0.63  fof(f230,plain,(
% 1.62/0.63    spl3_4 | ~spl3_5 | ~spl3_3),
% 1.62/0.63    inference(avatar_split_clause,[],[f228,f68,f107,f104])).
% 1.62/0.63  fof(f107,plain,(
% 1.62/0.63    spl3_5 <=> v1_relat_1(sK0)),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.62/0.63  fof(f68,plain,(
% 1.62/0.63    spl3_3 <=> r1_tarski(sK2,k1_relat_1(sK0))),
% 1.62/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.62/0.63  fof(f228,plain,(
% 1.62/0.63    ~v1_relat_1(sK0) | sK2 = k1_relat_1(k7_relat_1(sK0,sK2)) | ~spl3_3),
% 1.62/0.63    inference(resolution,[],[f69,f53])).
% 1.62/0.63  fof(f53,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = X0) )),
% 1.62/0.63    inference(cnf_transformation,[],[f29])).
% 1.62/0.63  fof(f29,plain,(
% 1.62/0.63    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.62/0.63    inference(flattening,[],[f28])).
% 1.62/0.63  fof(f28,plain,(
% 1.62/0.63    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f10])).
% 1.62/0.63  fof(f10,axiom,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).
% 1.62/0.63  fof(f69,plain,(
% 1.62/0.63    r1_tarski(sK2,k1_relat_1(sK0)) | ~spl3_3),
% 1.62/0.63    inference(avatar_component_clause,[],[f68])).
% 1.62/0.63  fof(f227,plain,(
% 1.62/0.63    ~spl3_5 | ~spl3_7 | spl3_3 | ~spl3_1),
% 1.62/0.63    inference(avatar_split_clause,[],[f226,f61,f68,f114,f107])).
% 1.62/0.63  fof(f226,plain,(
% 1.62/0.63    r1_tarski(sK2,k1_relat_1(sK0)) | ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | ~spl3_1),
% 1.62/0.63    inference(resolution,[],[f200,f46])).
% 1.62/0.63  fof(f46,plain,(
% 1.62/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f19])).
% 1.62/0.63  fof(f19,plain,(
% 1.62/0.63    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(ennf_transformation,[],[f7])).
% 1.62/0.63  fof(f7,axiom,(
% 1.62/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).
% 1.62/0.63  fof(f200,plain,(
% 1.62/0.63    ( ! [X0] : (~r1_tarski(k1_relat_1(k5_relat_1(sK0,sK1)),X0) | r1_tarski(sK2,X0)) ) | ~spl3_1),
% 1.62/0.63    inference(superposition,[],[f59,f122])).
% 1.62/0.63  fof(f122,plain,(
% 1.62/0.63    k1_relat_1(k5_relat_1(sK0,sK1)) = k2_xboole_0(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 1.62/0.63    inference(resolution,[],[f62,f55])).
% 1.62/0.63  fof(f55,plain,(
% 1.62/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.62/0.63    inference(cnf_transformation,[],[f31])).
% 1.62/0.63  fof(f31,plain,(
% 1.62/0.63    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.62/0.63    inference(ennf_transformation,[],[f2])).
% 1.62/0.63  fof(f2,axiom,(
% 1.62/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.62/0.63  fof(f62,plain,(
% 1.62/0.63    r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) | ~spl3_1),
% 1.62/0.63    inference(avatar_component_clause,[],[f61])).
% 1.62/0.63  fof(f59,plain,(
% 1.62/0.63    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f36])).
% 1.62/0.63  fof(f36,plain,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.62/0.63    inference(ennf_transformation,[],[f1])).
% 1.62/0.63  fof(f1,axiom,(
% 1.62/0.63    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.62/0.63  fof(f168,plain,(
% 1.62/0.63    spl3_10),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f167])).
% 1.62/0.63  fof(f167,plain,(
% 1.62/0.63    $false | spl3_10),
% 1.62/0.63    inference(resolution,[],[f155,f42])).
% 1.62/0.63  fof(f155,plain,(
% 1.62/0.63    ~v1_relat_1(sK0) | spl3_10),
% 1.62/0.63    inference(resolution,[],[f138,f49])).
% 1.62/0.63  fof(f49,plain,(
% 1.62/0.63    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f24])).
% 1.62/0.63  fof(f24,plain,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(ennf_transformation,[],[f4])).
% 1.62/0.63  fof(f4,axiom,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.62/0.63  fof(f138,plain,(
% 1.62/0.63    ~v1_relat_1(k7_relat_1(sK0,sK2)) | spl3_10),
% 1.62/0.63    inference(avatar_component_clause,[],[f137])).
% 1.62/0.63  fof(f131,plain,(
% 1.62/0.63    ~spl3_5 | ~spl3_7 | spl3_9),
% 1.62/0.63    inference(avatar_split_clause,[],[f130,f127,f114,f107])).
% 1.62/0.63  fof(f130,plain,(
% 1.62/0.63    ~v1_relat_1(sK1) | ~v1_relat_1(sK0) | spl3_9),
% 1.62/0.63    inference(resolution,[],[f128,f58])).
% 1.62/0.63  fof(f58,plain,(
% 1.62/0.63    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.62/0.63    inference(cnf_transformation,[],[f35])).
% 1.62/0.63  fof(f35,plain,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 1.62/0.63    inference(flattening,[],[f34])).
% 1.62/0.63  fof(f34,plain,(
% 1.62/0.63    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 1.62/0.63    inference(ennf_transformation,[],[f3])).
% 1.62/0.63  fof(f3,axiom,(
% 1.62/0.63    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 1.62/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 1.62/0.63  fof(f128,plain,(
% 1.62/0.63    ~v1_relat_1(k5_relat_1(sK0,sK1)) | spl3_9),
% 1.62/0.63    inference(avatar_component_clause,[],[f127])).
% 1.62/0.63  fof(f129,plain,(
% 1.62/0.63    spl3_8 | ~spl3_9 | ~spl3_1),
% 1.62/0.63    inference(avatar_split_clause,[],[f121,f61,f127,f124])).
% 1.62/0.63  fof(f121,plain,(
% 1.62/0.63    ~v1_relat_1(k5_relat_1(sK0,sK1)) | sK2 = k1_relat_1(k7_relat_1(k5_relat_1(sK0,sK1),sK2)) | ~spl3_1),
% 1.62/0.63    inference(resolution,[],[f62,f53])).
% 1.62/0.63  fof(f120,plain,(
% 1.62/0.63    spl3_7),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f119])).
% 1.62/0.63  fof(f119,plain,(
% 1.62/0.63    $false | spl3_7),
% 1.62/0.63    inference(resolution,[],[f115,f40])).
% 1.62/0.63  fof(f115,plain,(
% 1.62/0.63    ~v1_relat_1(sK1) | spl3_7),
% 1.62/0.63    inference(avatar_component_clause,[],[f114])).
% 1.62/0.63  fof(f118,plain,(
% 1.62/0.63    spl3_5),
% 1.62/0.63    inference(avatar_contradiction_clause,[],[f117])).
% 1.62/0.63  fof(f117,plain,(
% 1.62/0.63    $false | spl3_5),
% 1.62/0.63    inference(resolution,[],[f108,f42])).
% 1.62/0.63  fof(f108,plain,(
% 1.62/0.63    ~v1_relat_1(sK0) | spl3_5),
% 1.62/0.63    inference(avatar_component_clause,[],[f107])).
% 1.62/0.63  fof(f74,plain,(
% 1.62/0.63    ~spl3_1 | ~spl3_2 | ~spl3_3),
% 1.62/0.63    inference(avatar_split_clause,[],[f37,f68,f64,f61])).
% 1.62/0.63  fof(f37,plain,(
% 1.62/0.63    ~r1_tarski(sK2,k1_relat_1(sK0)) | ~r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | ~r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  fof(f70,plain,(
% 1.62/0.63    spl3_1 | spl3_3),
% 1.62/0.63    inference(avatar_split_clause,[],[f38,f68,f61])).
% 1.62/0.63  fof(f38,plain,(
% 1.62/0.63    r1_tarski(sK2,k1_relat_1(sK0)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  fof(f66,plain,(
% 1.62/0.63    spl3_1 | spl3_2),
% 1.62/0.63    inference(avatar_split_clause,[],[f39,f64,f61])).
% 1.62/0.63  fof(f39,plain,(
% 1.62/0.63    r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),
% 1.62/0.63    inference(cnf_transformation,[],[f18])).
% 1.62/0.63  % SZS output end Proof for theBenchmark
% 1.62/0.63  % (4835)------------------------------
% 1.62/0.63  % (4835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.63  % (4835)Termination reason: Refutation
% 1.62/0.63  
% 1.62/0.63  % (4835)Memory used [KB]: 13048
% 1.62/0.63  % (4835)Time elapsed: 0.216 s
% 1.62/0.63  % (4835)------------------------------
% 1.62/0.63  % (4835)------------------------------
% 1.62/0.63  % (4822)Success in time 0.267 s
%------------------------------------------------------------------------------
