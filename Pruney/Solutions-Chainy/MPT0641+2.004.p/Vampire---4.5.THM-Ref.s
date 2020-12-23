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
% DateTime   : Thu Dec  3 12:52:38 EST 2020

% Result     : Theorem 6.90s
% Output     : Refutation 6.90s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 484 expanded)
%              Number of leaves         :   18 (  98 expanded)
%              Depth                    :   29
%              Number of atoms          :  580 (2594 expanded)
%              Number of equality atoms :   79 ( 378 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10663,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f119,f131,f1665,f1683,f1688,f3069,f3076,f10662])).

fof(f10662,plain,
    ( spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(avatar_contradiction_clause,[],[f10661])).

fof(f10661,plain,
    ( $false
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(subsumption_resolution,[],[f10660,f65])).

fof(f65,plain,
    ( ~ v2_funct_1(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_1
  <=> v2_funct_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f10660,plain,
    ( v2_funct_1(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(subsumption_resolution,[],[f10659,f33])).

fof(f33,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_funct_1(X0)
            | ~ v2_funct_1(X1) )
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_funct_1(X0)
            | ~ v2_funct_1(X1) )
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(k5_relat_1(X1,X0))
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(k5_relat_1(X1,X0)) )
             => ( v2_funct_1(X0)
                & v2_funct_1(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f10659,plain,
    ( ~ v1_relat_1(sK0)
    | v2_funct_1(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(subsumption_resolution,[],[f10658,f34])).

fof(f34,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f10658,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(trivial_inequality_removal,[],[f10656])).

fof(f10656,plain,
    ( sK2(sK0) != sK2(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(superposition,[],[f41,f10566])).

fof(f10566,plain,
    ( sK2(sK0) = sK3(sK0)
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(forward_demodulation,[],[f10555,f1744])).

fof(f1744,plain,
    ( sK2(sK0) = k1_funct_1(sK1,sK5(sK1,sK2(sK0)))
    | ~ spl7_106 ),
    inference(resolution,[],[f582,f1687])).

fof(f1687,plain,
    ( r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | ~ spl7_106 ),
    inference(avatar_component_clause,[],[f1685])).

fof(f1685,plain,
    ( spl7_106
  <=> r2_hidden(sK2(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).

fof(f582,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | k1_funct_1(sK1,sK5(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f571,f29])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f571,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,sK5(sK1,X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f58,f30])).

fof(f30,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(X0,sK5(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK5(X0,X2)) = X2
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f10555,plain,
    ( sK3(sK0) = k1_funct_1(sK1,sK5(sK1,sK2(sK0)))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(backward_demodulation,[],[f1745,f10554])).

fof(f10554,plain,
    ( sK5(sK1,sK2(sK0)) = sK5(sK1,sK3(sK0))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(subsumption_resolution,[],[f10553,f2978])).

fof(f2978,plain,
    ( r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1))
    | ~ spl7_151 ),
    inference(avatar_component_clause,[],[f2977])).

fof(f2977,plain,
    ( spl7_151
  <=> r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).

fof(f10553,plain,
    ( ~ r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1))
    | sK5(sK1,sK2(sK0)) = sK5(sK1,sK3(sK0))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(trivial_inequality_removal,[],[f10543])).

fof(f10543,plain,
    ( k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(sK0,sK2(sK0))
    | ~ r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1))
    | sK5(sK1,sK2(sK0)) = sK5(sK1,sK3(sK0))
    | spl7_1
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_105
    | ~ spl7_106
    | ~ spl7_147
    | ~ spl7_151 ),
    inference(superposition,[],[f5633,f5612])).

fof(f5612,plain,
    ( k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK3(sK0)))
    | spl7_1
    | ~ spl7_105
    | ~ spl7_151 ),
    inference(forward_demodulation,[],[f5611,f1708])).

fof(f1708,plain,
    ( k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(sK0,sK3(sK0))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f1707,f33])).

fof(f1707,plain,
    ( k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(sK0,sK3(sK0))
    | ~ v1_relat_1(sK0)
    | spl7_1 ),
    inference(subsumption_resolution,[],[f1706,f34])).

fof(f1706,plain,
    ( ~ v1_funct_1(sK0)
    | k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(sK0,sK3(sK0))
    | ~ v1_relat_1(sK0)
    | spl7_1 ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f5611,plain,
    ( k1_funct_1(sK0,sK3(sK0)) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK3(sK0)))
    | ~ spl7_105
    | ~ spl7_151 ),
    inference(forward_demodulation,[],[f5600,f1745])).

fof(f5600,plain,
    ( k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,sK3(sK0)))) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK3(sK0)))
    | ~ spl7_151 ),
    inference(resolution,[],[f5556,f2978])).

fof(f5556,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK0),X0) ) ),
    inference(subsumption_resolution,[],[f5537,f29])).

fof(f5537,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X0,k1_relat_1(sK1))
      | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK0),X0) ) ),
    inference(resolution,[],[f2617,f30])).

fof(f2617,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | k1_funct_1(k5_relat_1(X2,sK0),X3) = k1_funct_1(sK0,k1_funct_1(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f2599,f33])).

fof(f2599,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | k1_funct_1(k5_relat_1(X2,sK0),X3) = k1_funct_1(sK0,k1_funct_1(X2,X3)) ) ),
    inference(resolution,[],[f51,f34])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))
          | ~ r2_hidden(X0,k1_relat_1(X1))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

fof(f5633,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | sK5(sK1,sK2(sK0)) = X1 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(subsumption_resolution,[],[f5632,f2956])).

fof(f2956,plain,
    ( r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1))
    | ~ spl7_147 ),
    inference(avatar_component_clause,[],[f2955])).

fof(f2955,plain,
    ( spl7_147
  <=> r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_147])])).

fof(f5632,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1))
        | ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | sK5(sK1,sK2(sK0)) = X1 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(forward_demodulation,[],[f5631,f97])).

fof(f97,plain,(
    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(forward_demodulation,[],[f94,f71])).

fof(f71,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(resolution,[],[f35,f29])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f94,plain,(
    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f90,f29])).

fof(f90,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,sK0)) = k10_relat_1(X1,k2_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f88,f32])).

fof(f32,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f88,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X1,sK0)) = k10_relat_1(X1,k1_relat_1(sK0)) ) ),
    inference(resolution,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).

fof(f5631,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_relat_1(sK1))
        | k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0)))
        | sK5(sK1,sK2(sK0)) = X1 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(forward_demodulation,[],[f5630,f97])).

fof(f5630,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0)))
        | sK5(sK1,sK2(sK0)) = X1 )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(subsumption_resolution,[],[f5629,f31])).

fof(f31,plain,(
    v2_funct_1(k5_relat_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f5629,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0)))
        | sK5(sK1,sK2(sK0)) = X1
        | ~ v2_funct_1(k5_relat_1(sK1,sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(subsumption_resolution,[],[f5628,f106])).

fof(f106,plain,
    ( v1_relat_1(k5_relat_1(sK1,sK0))
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl7_3
  <=> v1_relat_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f5628,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ v1_relat_1(k5_relat_1(sK1,sK0))
        | sK5(sK1,sK2(sK0)) = X1
        | ~ v2_funct_1(k5_relat_1(sK1,sK0)) )
    | ~ spl7_4
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(subsumption_resolution,[],[f5620,f110])).

fof(f110,plain,
    ( v1_funct_1(k5_relat_1(sK1,sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl7_4
  <=> v1_funct_1(k5_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f5620,plain,
    ( ! [X1] :
        ( k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1)
        | ~ v1_funct_1(k5_relat_1(sK1,sK0))
        | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0)))
        | ~ v1_relat_1(k5_relat_1(sK1,sK0))
        | sK5(sK1,sK2(sK0)) = X1
        | ~ v2_funct_1(k5_relat_1(sK1,sK0)) )
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(superposition,[],[f37,f5610])).

fof(f5610,plain,
    ( k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK2(sK0)))
    | ~ spl7_106
    | ~ spl7_147 ),
    inference(forward_demodulation,[],[f5599,f1744])).

fof(f5599,plain,
    ( k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,sK2(sK0)))) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK2(sK0)))
    | ~ spl7_147 ),
    inference(resolution,[],[f5556,f2956])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1745,plain,
    ( sK3(sK0) = k1_funct_1(sK1,sK5(sK1,sK3(sK0)))
    | ~ spl7_105 ),
    inference(resolution,[],[f582,f1682])).

fof(f1682,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | ~ spl7_105 ),
    inference(avatar_component_clause,[],[f1680])).

fof(f1680,plain,
    ( spl7_105
  <=> r2_hidden(sK3(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f41,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3076,plain,
    ( ~ spl7_105
    | spl7_151 ),
    inference(avatar_contradiction_clause,[],[f3075])).

fof(f3075,plain,
    ( $false
    | ~ spl7_105
    | spl7_151 ),
    inference(subsumption_resolution,[],[f3074,f1682])).

fof(f3074,plain,
    ( ~ r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | spl7_151 ),
    inference(subsumption_resolution,[],[f3073,f29])).

fof(f3073,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | spl7_151 ),
    inference(subsumption_resolution,[],[f3072,f30])).

fof(f3072,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | spl7_151 ),
    inference(resolution,[],[f2979,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK5(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2979,plain,
    ( ~ r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1))
    | spl7_151 ),
    inference(avatar_component_clause,[],[f2977])).

fof(f3069,plain,
    ( ~ spl7_106
    | spl7_147 ),
    inference(avatar_contradiction_clause,[],[f3068])).

fof(f3068,plain,
    ( $false
    | ~ spl7_106
    | spl7_147 ),
    inference(subsumption_resolution,[],[f3067,f1687])).

fof(f3067,plain,
    ( ~ r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | spl7_147 ),
    inference(subsumption_resolution,[],[f3066,f29])).

fof(f3066,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | spl7_147 ),
    inference(subsumption_resolution,[],[f3065,f30])).

fof(f3065,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1)
    | ~ r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | spl7_147 ),
    inference(resolution,[],[f2957,f59])).

fof(f2957,plain,
    ( ~ r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1))
    | spl7_147 ),
    inference(avatar_component_clause,[],[f2955])).

fof(f1688,plain,
    ( spl7_1
    | spl7_106 ),
    inference(avatar_split_clause,[],[f78,f1685,f63])).

fof(f78,plain,
    ( r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | v2_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f77,f33])).

fof(f77,plain,
    ( r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,
    ( r2_hidden(sK2(sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0) ),
    inference(superposition,[],[f38,f32])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1683,plain,
    ( spl7_1
    | spl7_105 ),
    inference(avatar_split_clause,[],[f82,f1680,f63])).

fof(f82,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | v2_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f81,f33])).

fof(f81,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,
    ( r2_hidden(sK3(sK0),k2_relat_1(sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | v2_funct_1(sK0) ),
    inference(superposition,[],[f39,f32])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f1665,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f1664])).

fof(f1664,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f1663,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1663,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1))
    | spl7_2 ),
    inference(backward_demodulation,[],[f1659,f32])).

fof(f1659,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f1647,f69])).

fof(f69,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl7_2
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1647,plain,
    ( ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1646,f33])).

fof(f1646,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1645,f30])).

fof(f1645,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f1644,f29])).

fof(f1644,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | v2_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f733,f34])).

fof(f733,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0))
    | v2_funct_1(sK1) ),
    inference(resolution,[],[f42,f31])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

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
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
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
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

fof(f131,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f129,f29])).

fof(f129,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f128,f34])).

fof(f128,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f127,f33])).

fof(f127,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl7_4 ),
    inference(subsumption_resolution,[],[f126,f30])).

fof(f126,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl7_4 ),
    inference(resolution,[],[f111,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f111,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK0))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f119,plain,(
    spl7_3 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl7_3 ),
    inference(subsumption_resolution,[],[f117,f29])).

fof(f117,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_3 ),
    inference(subsumption_resolution,[],[f116,f33])).

fof(f116,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(sK1)
    | spl7_3 ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f107,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK0))
    | spl7_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f70,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f28,f67,f63])).

fof(f28,plain,
    ( ~ v2_funct_1(sK1)
    | ~ v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (25990)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (26000)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (25987)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (26003)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.52  % (26011)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.52  % (25991)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.52  % (26010)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (25996)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.53  % (26001)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (26004)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (25989)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (25997)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (26002)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (25998)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (25995)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (26005)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.53  % (25988)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (25994)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (26012)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.54  % (25992)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (26008)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (26006)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.54  % (26009)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (25999)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (25993)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (26007)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.79/0.62  % (25996)Refutation not found, incomplete strategy% (25996)------------------------------
% 1.79/0.62  % (25996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.62  % (25996)Termination reason: Refutation not found, incomplete strategy
% 1.79/0.62  
% 1.79/0.62  % (25996)Memory used [KB]: 6140
% 1.79/0.62  % (25996)Time elapsed: 0.209 s
% 1.79/0.62  % (25996)------------------------------
% 1.79/0.62  % (25996)------------------------------
% 4.12/0.92  % (26001)Time limit reached!
% 4.12/0.92  % (26001)------------------------------
% 4.12/0.92  % (26001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.12/0.92  % (26001)Termination reason: Time limit
% 4.12/0.92  
% 4.12/0.92  % (26001)Memory used [KB]: 8187
% 4.12/0.92  % (26001)Time elapsed: 0.506 s
% 4.12/0.92  % (26001)------------------------------
% 4.12/0.92  % (26001)------------------------------
% 4.50/0.93  % (26000)Time limit reached!
% 4.50/0.93  % (26000)------------------------------
% 4.50/0.93  % (26000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.50/0.93  % (26000)Termination reason: Time limit
% 4.50/0.93  % (26000)Termination phase: Saturation
% 4.50/0.93  
% 4.50/0.93  % (26000)Memory used [KB]: 19189
% 4.50/0.93  % (26000)Time elapsed: 0.500 s
% 4.50/0.93  % (26000)------------------------------
% 4.50/0.93  % (26000)------------------------------
% 4.55/0.94  % (25987)Time limit reached!
% 4.55/0.94  % (25987)------------------------------
% 4.55/0.94  % (25987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.55/0.94  % (25987)Termination reason: Time limit
% 4.55/0.94  
% 4.55/0.94  % (25987)Memory used [KB]: 18677
% 4.55/0.94  % (25987)Time elapsed: 0.521 s
% 4.55/0.94  % (25987)------------------------------
% 4.55/0.94  % (25987)------------------------------
% 5.04/1.02  % (25993)Time limit reached!
% 5.04/1.02  % (25993)------------------------------
% 5.04/1.02  % (25993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.02  % (25993)Termination reason: Time limit
% 5.04/1.02  % (25993)Termination phase: Saturation
% 5.04/1.02  
% 5.04/1.02  % (25993)Memory used [KB]: 16758
% 5.04/1.02  % (25993)Time elapsed: 0.600 s
% 5.04/1.02  % (25993)------------------------------
% 5.04/1.02  % (25993)------------------------------
% 6.90/1.27  % (26009)Refutation found. Thanks to Tanya!
% 6.90/1.27  % SZS status Theorem for theBenchmark
% 6.90/1.27  % SZS output start Proof for theBenchmark
% 6.90/1.27  fof(f10663,plain,(
% 6.90/1.27    $false),
% 6.90/1.27    inference(avatar_sat_refutation,[],[f70,f119,f131,f1665,f1683,f1688,f3069,f3076,f10662])).
% 6.90/1.27  fof(f10662,plain,(
% 6.90/1.27    spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151),
% 6.90/1.27    inference(avatar_contradiction_clause,[],[f10661])).
% 6.90/1.27  fof(f10661,plain,(
% 6.90/1.27    $false | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(subsumption_resolution,[],[f10660,f65])).
% 6.90/1.27  fof(f65,plain,(
% 6.90/1.27    ~v2_funct_1(sK0) | spl7_1),
% 6.90/1.27    inference(avatar_component_clause,[],[f63])).
% 6.90/1.27  fof(f63,plain,(
% 6.90/1.27    spl7_1 <=> v2_funct_1(sK0)),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 6.90/1.27  fof(f10660,plain,(
% 6.90/1.27    v2_funct_1(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(subsumption_resolution,[],[f10659,f33])).
% 6.90/1.27  fof(f33,plain,(
% 6.90/1.27    v1_relat_1(sK0)),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  fof(f13,plain,(
% 6.90/1.27    ? [X0] : (? [X1] : ((~v2_funct_1(X0) | ~v2_funct_1(X1)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 6.90/1.27    inference(flattening,[],[f12])).
% 6.90/1.27  fof(f12,plain,(
% 6.90/1.27    ? [X0] : (? [X1] : (((~v2_funct_1(X0) | ~v2_funct_1(X1)) & (k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0)))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 6.90/1.27    inference(ennf_transformation,[],[f11])).
% 6.90/1.27  fof(f11,negated_conjecture,(
% 6.90/1.27    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 6.90/1.27    inference(negated_conjecture,[],[f10])).
% 6.90/1.27  fof(f10,conjecture,(
% 6.90/1.27    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 6.90/1.27  fof(f10659,plain,(
% 6.90/1.27    ~v1_relat_1(sK0) | v2_funct_1(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(subsumption_resolution,[],[f10658,f34])).
% 6.90/1.27  fof(f34,plain,(
% 6.90/1.27    v1_funct_1(sK0)),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  fof(f10658,plain,(
% 6.90/1.27    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | v2_funct_1(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(trivial_inequality_removal,[],[f10656])).
% 6.90/1.27  fof(f10656,plain,(
% 6.90/1.27    sK2(sK0) != sK2(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | v2_funct_1(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(superposition,[],[f41,f10566])).
% 6.90/1.27  fof(f10566,plain,(
% 6.90/1.27    sK2(sK0) = sK3(sK0) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(forward_demodulation,[],[f10555,f1744])).
% 6.90/1.27  fof(f1744,plain,(
% 6.90/1.27    sK2(sK0) = k1_funct_1(sK1,sK5(sK1,sK2(sK0))) | ~spl7_106),
% 6.90/1.27    inference(resolution,[],[f582,f1687])).
% 6.90/1.27  fof(f1687,plain,(
% 6.90/1.27    r2_hidden(sK2(sK0),k2_relat_1(sK1)) | ~spl7_106),
% 6.90/1.27    inference(avatar_component_clause,[],[f1685])).
% 6.90/1.27  fof(f1685,plain,(
% 6.90/1.27    spl7_106 <=> r2_hidden(sK2(sK0),k2_relat_1(sK1))),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_106])])).
% 6.90/1.27  fof(f582,plain,(
% 6.90/1.27    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | k1_funct_1(sK1,sK5(sK1,X0)) = X0) )),
% 6.90/1.27    inference(subsumption_resolution,[],[f571,f29])).
% 6.90/1.27  fof(f29,plain,(
% 6.90/1.27    v1_relat_1(sK1)),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  fof(f571,plain,(
% 6.90/1.27    ( ! [X0] : (~v1_relat_1(sK1) | k1_funct_1(sK1,sK5(sK1,X0)) = X0 | ~r2_hidden(X0,k2_relat_1(sK1))) )),
% 6.90/1.27    inference(resolution,[],[f58,f30])).
% 6.90/1.27  fof(f30,plain,(
% 6.90/1.27    v1_funct_1(sK1)),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  fof(f58,plain,(
% 6.90/1.27    ( ! [X2,X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK5(X0,X2)) = X2 | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 6.90/1.27    inference(equality_resolution,[],[f47])).
% 6.90/1.27  fof(f47,plain,(
% 6.90/1.27    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK5(X0,X2)) = X2 | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 6.90/1.27    inference(cnf_transformation,[],[f21])).
% 6.90/1.27  fof(f21,plain,(
% 6.90/1.27    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(flattening,[],[f20])).
% 6.90/1.27  fof(f20,plain,(
% 6.90/1.27    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.90/1.27    inference(ennf_transformation,[],[f5])).
% 6.90/1.27  fof(f5,axiom,(
% 6.90/1.27    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).
% 6.90/1.27  fof(f10555,plain,(
% 6.90/1.27    sK3(sK0) = k1_funct_1(sK1,sK5(sK1,sK2(sK0))) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(backward_demodulation,[],[f1745,f10554])).
% 6.90/1.27  fof(f10554,plain,(
% 6.90/1.27    sK5(sK1,sK2(sK0)) = sK5(sK1,sK3(sK0)) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(subsumption_resolution,[],[f10553,f2978])).
% 6.90/1.27  fof(f2978,plain,(
% 6.90/1.27    r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1)) | ~spl7_151),
% 6.90/1.27    inference(avatar_component_clause,[],[f2977])).
% 6.90/1.27  fof(f2977,plain,(
% 6.90/1.27    spl7_151 <=> r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1))),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_151])])).
% 6.90/1.27  fof(f10553,plain,(
% 6.90/1.27    ~r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1)) | sK5(sK1,sK2(sK0)) = sK5(sK1,sK3(sK0)) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(trivial_inequality_removal,[],[f10543])).
% 6.90/1.27  fof(f10543,plain,(
% 6.90/1.27    k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(sK0,sK2(sK0)) | ~r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1)) | sK5(sK1,sK2(sK0)) = sK5(sK1,sK3(sK0)) | (spl7_1 | ~spl7_3 | ~spl7_4 | ~spl7_105 | ~spl7_106 | ~spl7_147 | ~spl7_151)),
% 6.90/1.27    inference(superposition,[],[f5633,f5612])).
% 6.90/1.27  fof(f5612,plain,(
% 6.90/1.27    k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK3(sK0))) | (spl7_1 | ~spl7_105 | ~spl7_151)),
% 6.90/1.27    inference(forward_demodulation,[],[f5611,f1708])).
% 6.90/1.27  fof(f1708,plain,(
% 6.90/1.27    k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(sK0,sK3(sK0)) | spl7_1),
% 6.90/1.27    inference(subsumption_resolution,[],[f1707,f33])).
% 6.90/1.27  fof(f1707,plain,(
% 6.90/1.27    k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(sK0,sK3(sK0)) | ~v1_relat_1(sK0) | spl7_1),
% 6.90/1.27    inference(subsumption_resolution,[],[f1706,f34])).
% 6.90/1.27  fof(f1706,plain,(
% 6.90/1.27    ~v1_funct_1(sK0) | k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(sK0,sK3(sK0)) | ~v1_relat_1(sK0) | spl7_1),
% 6.90/1.27    inference(resolution,[],[f65,f40])).
% 6.90/1.27  fof(f40,plain,(
% 6.90/1.27    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK2(X0)) = k1_funct_1(X0,sK3(X0)) | ~v1_relat_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f17])).
% 6.90/1.27  fof(f17,plain,(
% 6.90/1.27    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(flattening,[],[f16])).
% 6.90/1.27  fof(f16,plain,(
% 6.90/1.27    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.90/1.27    inference(ennf_transformation,[],[f6])).
% 6.90/1.27  fof(f6,axiom,(
% 6.90/1.27    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 6.90/1.27  fof(f5611,plain,(
% 6.90/1.27    k1_funct_1(sK0,sK3(sK0)) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK3(sK0))) | (~spl7_105 | ~spl7_151)),
% 6.90/1.27    inference(forward_demodulation,[],[f5600,f1745])).
% 6.90/1.27  fof(f5600,plain,(
% 6.90/1.27    k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,sK3(sK0)))) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK3(sK0))) | ~spl7_151),
% 6.90/1.27    inference(resolution,[],[f5556,f2978])).
% 6.90/1.27  fof(f5556,plain,(
% 6.90/1.27    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK0),X0)) )),
% 6.90/1.27    inference(subsumption_resolution,[],[f5537,f29])).
% 6.90/1.27  fof(f5537,plain,(
% 6.90/1.27    ( ! [X0] : (~v1_relat_1(sK1) | ~r2_hidden(X0,k1_relat_1(sK1)) | k1_funct_1(sK0,k1_funct_1(sK1,X0)) = k1_funct_1(k5_relat_1(sK1,sK0),X0)) )),
% 6.90/1.27    inference(resolution,[],[f2617,f30])).
% 6.90/1.27  fof(f2617,plain,(
% 6.90/1.27    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(k5_relat_1(X2,sK0),X3) = k1_funct_1(sK0,k1_funct_1(X2,X3))) )),
% 6.90/1.27    inference(subsumption_resolution,[],[f2599,f33])).
% 6.90/1.27  fof(f2599,plain,(
% 6.90/1.27    ( ! [X2,X3] : (~v1_funct_1(X2) | ~v1_relat_1(sK0) | ~v1_relat_1(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | k1_funct_1(k5_relat_1(X2,sK0),X3) = k1_funct_1(sK0,k1_funct_1(X2,X3))) )),
% 6.90/1.27    inference(resolution,[],[f51,f34])).
% 6.90/1.27  fof(f51,plain,(
% 6.90/1.27    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0))) )),
% 6.90/1.27    inference(cnf_transformation,[],[f25])).
% 6.90/1.27  fof(f25,plain,(
% 6.90/1.27    ! [X0,X1] : (! [X2] : (k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 6.90/1.27    inference(flattening,[],[f24])).
% 6.90/1.27  fof(f24,plain,(
% 6.90/1.27    ! [X0,X1] : (! [X2] : ((k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 6.90/1.27    inference(ennf_transformation,[],[f8])).
% 6.90/1.27  fof(f8,axiom,(
% 6.90/1.27    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_funct_1(k5_relat_1(X1,X2),X0) = k1_funct_1(X2,k1_funct_1(X1,X0)))))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).
% 6.90/1.27  fof(f5633,plain,(
% 6.90/1.27    ( ! [X1] : (k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | ~r2_hidden(X1,k1_relat_1(sK1)) | sK5(sK1,sK2(sK0)) = X1) ) | (~spl7_3 | ~spl7_4 | ~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(subsumption_resolution,[],[f5632,f2956])).
% 6.90/1.27  fof(f2956,plain,(
% 6.90/1.27    r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1)) | ~spl7_147),
% 6.90/1.27    inference(avatar_component_clause,[],[f2955])).
% 6.90/1.27  fof(f2955,plain,(
% 6.90/1.27    spl7_147 <=> r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1))),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_147])])).
% 6.90/1.27  fof(f5632,plain,(
% 6.90/1.27    ( ! [X1] : (~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1)) | ~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | sK5(sK1,sK2(sK0)) = X1) ) | (~spl7_3 | ~spl7_4 | ~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(forward_demodulation,[],[f5631,f97])).
% 6.90/1.27  fof(f97,plain,(
% 6.90/1.27    k1_relat_1(sK1) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 6.90/1.27    inference(forward_demodulation,[],[f94,f71])).
% 6.90/1.27  fof(f71,plain,(
% 6.90/1.27    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1)),
% 6.90/1.27    inference(resolution,[],[f35,f29])).
% 6.90/1.27  fof(f35,plain,(
% 6.90/1.27    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f14])).
% 6.90/1.27  fof(f14,plain,(
% 6.90/1.27    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(ennf_transformation,[],[f3])).
% 6.90/1.27  fof(f3,axiom,(
% 6.90/1.27    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 6.90/1.27  fof(f94,plain,(
% 6.90/1.27    k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(k5_relat_1(sK1,sK0))),
% 6.90/1.27    inference(resolution,[],[f90,f29])).
% 6.90/1.27  fof(f90,plain,(
% 6.90/1.27    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,sK0)) = k10_relat_1(X1,k2_relat_1(sK1))) )),
% 6.90/1.27    inference(forward_demodulation,[],[f88,f32])).
% 6.90/1.27  fof(f32,plain,(
% 6.90/1.27    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  fof(f88,plain,(
% 6.90/1.27    ( ! [X1] : (~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X1,sK0)) = k10_relat_1(X1,k1_relat_1(sK0))) )),
% 6.90/1.27    inference(resolution,[],[f36,f33])).
% 6.90/1.27  fof(f36,plain,(
% 6.90/1.27    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X0) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 6.90/1.27    inference(cnf_transformation,[],[f15])).
% 6.90/1.27  fof(f15,plain,(
% 6.90/1.27    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(ennf_transformation,[],[f4])).
% 6.90/1.27  fof(f4,axiom,(
% 6.90/1.27    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t182_relat_1)).
% 6.90/1.27  fof(f5631,plain,(
% 6.90/1.27    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(sK1)) | k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | ~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0))) | sK5(sK1,sK2(sK0)) = X1) ) | (~spl7_3 | ~spl7_4 | ~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(forward_demodulation,[],[f5630,f97])).
% 6.90/1.27  fof(f5630,plain,(
% 6.90/1.27    ( ! [X1] : (k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0))) | ~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0))) | sK5(sK1,sK2(sK0)) = X1) ) | (~spl7_3 | ~spl7_4 | ~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(subsumption_resolution,[],[f5629,f31])).
% 6.90/1.27  fof(f31,plain,(
% 6.90/1.27    v2_funct_1(k5_relat_1(sK1,sK0))),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  fof(f5629,plain,(
% 6.90/1.27    ( ! [X1] : (k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0))) | ~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0))) | sK5(sK1,sK2(sK0)) = X1 | ~v2_funct_1(k5_relat_1(sK1,sK0))) ) | (~spl7_3 | ~spl7_4 | ~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(subsumption_resolution,[],[f5628,f106])).
% 6.90/1.27  fof(f106,plain,(
% 6.90/1.27    v1_relat_1(k5_relat_1(sK1,sK0)) | ~spl7_3),
% 6.90/1.27    inference(avatar_component_clause,[],[f105])).
% 6.90/1.27  fof(f105,plain,(
% 6.90/1.27    spl7_3 <=> v1_relat_1(k5_relat_1(sK1,sK0))),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 6.90/1.27  fof(f5628,plain,(
% 6.90/1.27    ( ! [X1] : (k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0))) | ~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0))) | ~v1_relat_1(k5_relat_1(sK1,sK0)) | sK5(sK1,sK2(sK0)) = X1 | ~v2_funct_1(k5_relat_1(sK1,sK0))) ) | (~spl7_4 | ~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(subsumption_resolution,[],[f5620,f110])).
% 6.90/1.27  fof(f110,plain,(
% 6.90/1.27    v1_funct_1(k5_relat_1(sK1,sK0)) | ~spl7_4),
% 6.90/1.27    inference(avatar_component_clause,[],[f109])).
% 6.90/1.27  fof(f109,plain,(
% 6.90/1.27    spl7_4 <=> v1_funct_1(k5_relat_1(sK1,sK0))),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 6.90/1.27  fof(f5620,plain,(
% 6.90/1.27    ( ! [X1] : (k1_funct_1(sK0,sK2(sK0)) != k1_funct_1(k5_relat_1(sK1,sK0),X1) | ~v1_funct_1(k5_relat_1(sK1,sK0)) | ~r2_hidden(X1,k1_relat_1(k5_relat_1(sK1,sK0))) | ~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(k5_relat_1(sK1,sK0))) | ~v1_relat_1(k5_relat_1(sK1,sK0)) | sK5(sK1,sK2(sK0)) = X1 | ~v2_funct_1(k5_relat_1(sK1,sK0))) ) | (~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(superposition,[],[f37,f5610])).
% 6.90/1.27  fof(f5610,plain,(
% 6.90/1.27    k1_funct_1(sK0,sK2(sK0)) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK2(sK0))) | (~spl7_106 | ~spl7_147)),
% 6.90/1.27    inference(forward_demodulation,[],[f5599,f1744])).
% 6.90/1.27  fof(f5599,plain,(
% 6.90/1.27    k1_funct_1(sK0,k1_funct_1(sK1,sK5(sK1,sK2(sK0)))) = k1_funct_1(k5_relat_1(sK1,sK0),sK5(sK1,sK2(sK0))) | ~spl7_147),
% 6.90/1.27    inference(resolution,[],[f5556,f2956])).
% 6.90/1.27  fof(f37,plain,(
% 6.90/1.27    ( ! [X2,X0,X1] : (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | ~v1_relat_1(X0) | X1 = X2 | ~v2_funct_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f17])).
% 6.90/1.27  fof(f1745,plain,(
% 6.90/1.27    sK3(sK0) = k1_funct_1(sK1,sK5(sK1,sK3(sK0))) | ~spl7_105),
% 6.90/1.27    inference(resolution,[],[f582,f1682])).
% 6.90/1.27  fof(f1682,plain,(
% 6.90/1.27    r2_hidden(sK3(sK0),k2_relat_1(sK1)) | ~spl7_105),
% 6.90/1.27    inference(avatar_component_clause,[],[f1680])).
% 6.90/1.27  fof(f1680,plain,(
% 6.90/1.27    spl7_105 <=> r2_hidden(sK3(sK0),k2_relat_1(sK1))),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).
% 6.90/1.27  fof(f41,plain,(
% 6.90/1.27    ( ! [X0] : (sK2(X0) != sK3(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f17])).
% 6.90/1.27  fof(f3076,plain,(
% 6.90/1.27    ~spl7_105 | spl7_151),
% 6.90/1.27    inference(avatar_contradiction_clause,[],[f3075])).
% 6.90/1.27  fof(f3075,plain,(
% 6.90/1.27    $false | (~spl7_105 | spl7_151)),
% 6.90/1.27    inference(subsumption_resolution,[],[f3074,f1682])).
% 6.90/1.27  fof(f3074,plain,(
% 6.90/1.27    ~r2_hidden(sK3(sK0),k2_relat_1(sK1)) | spl7_151),
% 6.90/1.27    inference(subsumption_resolution,[],[f3073,f29])).
% 6.90/1.27  fof(f3073,plain,(
% 6.90/1.27    ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK0),k2_relat_1(sK1)) | spl7_151),
% 6.90/1.27    inference(subsumption_resolution,[],[f3072,f30])).
% 6.90/1.27  fof(f3072,plain,(
% 6.90/1.27    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK3(sK0),k2_relat_1(sK1)) | spl7_151),
% 6.90/1.27    inference(resolution,[],[f2979,f59])).
% 6.90/1.27  fof(f59,plain,(
% 6.90/1.27    ( ! [X2,X0] : (r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 6.90/1.27    inference(equality_resolution,[],[f46])).
% 6.90/1.27  fof(f46,plain,(
% 6.90/1.27    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK5(X0,X2),k1_relat_1(X0)) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 6.90/1.27    inference(cnf_transformation,[],[f21])).
% 6.90/1.27  fof(f2979,plain,(
% 6.90/1.27    ~r2_hidden(sK5(sK1,sK3(sK0)),k1_relat_1(sK1)) | spl7_151),
% 6.90/1.27    inference(avatar_component_clause,[],[f2977])).
% 6.90/1.27  fof(f3069,plain,(
% 6.90/1.27    ~spl7_106 | spl7_147),
% 6.90/1.27    inference(avatar_contradiction_clause,[],[f3068])).
% 6.90/1.27  fof(f3068,plain,(
% 6.90/1.27    $false | (~spl7_106 | spl7_147)),
% 6.90/1.27    inference(subsumption_resolution,[],[f3067,f1687])).
% 6.90/1.27  fof(f3067,plain,(
% 6.90/1.27    ~r2_hidden(sK2(sK0),k2_relat_1(sK1)) | spl7_147),
% 6.90/1.27    inference(subsumption_resolution,[],[f3066,f29])).
% 6.90/1.27  fof(f3066,plain,(
% 6.90/1.27    ~v1_relat_1(sK1) | ~r2_hidden(sK2(sK0),k2_relat_1(sK1)) | spl7_147),
% 6.90/1.27    inference(subsumption_resolution,[],[f3065,f30])).
% 6.90/1.27  fof(f3065,plain,(
% 6.90/1.27    ~v1_funct_1(sK1) | ~v1_relat_1(sK1) | ~r2_hidden(sK2(sK0),k2_relat_1(sK1)) | spl7_147),
% 6.90/1.27    inference(resolution,[],[f2957,f59])).
% 6.90/1.27  fof(f2957,plain,(
% 6.90/1.27    ~r2_hidden(sK5(sK1,sK2(sK0)),k1_relat_1(sK1)) | spl7_147),
% 6.90/1.27    inference(avatar_component_clause,[],[f2955])).
% 6.90/1.27  fof(f1688,plain,(
% 6.90/1.27    spl7_1 | spl7_106),
% 6.90/1.27    inference(avatar_split_clause,[],[f78,f1685,f63])).
% 6.90/1.27  fof(f78,plain,(
% 6.90/1.27    r2_hidden(sK2(sK0),k2_relat_1(sK1)) | v2_funct_1(sK0)),
% 6.90/1.27    inference(subsumption_resolution,[],[f77,f33])).
% 6.90/1.27  fof(f77,plain,(
% 6.90/1.27    r2_hidden(sK2(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK0) | v2_funct_1(sK0)),
% 6.90/1.27    inference(subsumption_resolution,[],[f76,f34])).
% 6.90/1.27  fof(f76,plain,(
% 6.90/1.27    r2_hidden(sK2(sK0),k2_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | v2_funct_1(sK0)),
% 6.90/1.27    inference(superposition,[],[f38,f32])).
% 6.90/1.27  fof(f38,plain,(
% 6.90/1.27    ( ! [X0] : (r2_hidden(sK2(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f17])).
% 6.90/1.27  fof(f1683,plain,(
% 6.90/1.27    spl7_1 | spl7_105),
% 6.90/1.27    inference(avatar_split_clause,[],[f82,f1680,f63])).
% 6.90/1.27  fof(f82,plain,(
% 6.90/1.27    r2_hidden(sK3(sK0),k2_relat_1(sK1)) | v2_funct_1(sK0)),
% 6.90/1.27    inference(subsumption_resolution,[],[f81,f33])).
% 6.90/1.27  fof(f81,plain,(
% 6.90/1.27    r2_hidden(sK3(sK0),k2_relat_1(sK1)) | ~v1_relat_1(sK0) | v2_funct_1(sK0)),
% 6.90/1.27    inference(subsumption_resolution,[],[f80,f34])).
% 6.90/1.27  fof(f80,plain,(
% 6.90/1.27    r2_hidden(sK3(sK0),k2_relat_1(sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | v2_funct_1(sK0)),
% 6.90/1.27    inference(superposition,[],[f39,f32])).
% 6.90/1.27  fof(f39,plain,(
% 6.90/1.27    ( ! [X0] : (r2_hidden(sK3(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f17])).
% 6.90/1.27  fof(f1665,plain,(
% 6.90/1.27    spl7_2),
% 6.90/1.27    inference(avatar_contradiction_clause,[],[f1664])).
% 6.90/1.27  fof(f1664,plain,(
% 6.90/1.27    $false | spl7_2),
% 6.90/1.27    inference(subsumption_resolution,[],[f1663,f60])).
% 6.90/1.27  fof(f60,plain,(
% 6.90/1.27    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.90/1.27    inference(equality_resolution,[],[f54])).
% 6.90/1.27  fof(f54,plain,(
% 6.90/1.27    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.90/1.27    inference(cnf_transformation,[],[f1])).
% 6.90/1.27  fof(f1,axiom,(
% 6.90/1.27    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.90/1.27  fof(f1663,plain,(
% 6.90/1.27    ~r1_tarski(k2_relat_1(sK1),k2_relat_1(sK1)) | spl7_2),
% 6.90/1.27    inference(backward_demodulation,[],[f1659,f32])).
% 6.90/1.27  fof(f1659,plain,(
% 6.90/1.27    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | spl7_2),
% 6.90/1.27    inference(subsumption_resolution,[],[f1647,f69])).
% 6.90/1.27  fof(f69,plain,(
% 6.90/1.27    ~v2_funct_1(sK1) | spl7_2),
% 6.90/1.27    inference(avatar_component_clause,[],[f67])).
% 6.90/1.27  fof(f67,plain,(
% 6.90/1.27    spl7_2 <=> v2_funct_1(sK1)),
% 6.90/1.27    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 6.90/1.27  fof(f1647,plain,(
% 6.90/1.27    ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | v2_funct_1(sK1)),
% 6.90/1.27    inference(subsumption_resolution,[],[f1646,f33])).
% 6.90/1.27  fof(f1646,plain,(
% 6.90/1.27    ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | v2_funct_1(sK1)),
% 6.90/1.27    inference(subsumption_resolution,[],[f1645,f30])).
% 6.90/1.27  fof(f1645,plain,(
% 6.90/1.27    ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | v2_funct_1(sK1)),
% 6.90/1.27    inference(subsumption_resolution,[],[f1644,f29])).
% 6.90/1.27  fof(f1644,plain,(
% 6.90/1.27    ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | v2_funct_1(sK1)),
% 6.90/1.27    inference(subsumption_resolution,[],[f733,f34])).
% 6.90/1.27  fof(f733,plain,(
% 6.90/1.27    ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~r1_tarski(k2_relat_1(sK1),k1_relat_1(sK0)) | v2_funct_1(sK1)),
% 6.90/1.27    inference(resolution,[],[f42,f31])).
% 6.90/1.27  fof(f42,plain,(
% 6.90/1.27    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | v2_funct_1(X1)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f19])).
% 6.90/1.27  fof(f19,plain,(
% 6.90/1.27    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(flattening,[],[f18])).
% 6.90/1.27  fof(f18,plain,(
% 6.90/1.27    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.90/1.27    inference(ennf_transformation,[],[f9])).
% 6.90/1.27  fof(f9,axiom,(
% 6.90/1.27    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).
% 6.90/1.27  fof(f131,plain,(
% 6.90/1.27    spl7_4),
% 6.90/1.27    inference(avatar_contradiction_clause,[],[f130])).
% 6.90/1.27  fof(f130,plain,(
% 6.90/1.27    $false | spl7_4),
% 6.90/1.27    inference(subsumption_resolution,[],[f129,f29])).
% 6.90/1.27  fof(f129,plain,(
% 6.90/1.27    ~v1_relat_1(sK1) | spl7_4),
% 6.90/1.27    inference(subsumption_resolution,[],[f128,f34])).
% 6.90/1.27  fof(f128,plain,(
% 6.90/1.27    ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | spl7_4),
% 6.90/1.27    inference(subsumption_resolution,[],[f127,f33])).
% 6.90/1.27  fof(f127,plain,(
% 6.90/1.27    ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | spl7_4),
% 6.90/1.27    inference(subsumption_resolution,[],[f126,f30])).
% 6.90/1.27  fof(f126,plain,(
% 6.90/1.27    ~v1_funct_1(sK1) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK1) | spl7_4),
% 6.90/1.27    inference(resolution,[],[f111,f50])).
% 6.90/1.27  fof(f50,plain,(
% 6.90/1.27    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f23])).
% 6.90/1.27  fof(f23,plain,(
% 6.90/1.27    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(flattening,[],[f22])).
% 6.90/1.27  fof(f22,plain,(
% 6.90/1.27    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.90/1.27    inference(ennf_transformation,[],[f7])).
% 6.90/1.27  fof(f7,axiom,(
% 6.90/1.27    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_funct_1)).
% 6.90/1.27  fof(f111,plain,(
% 6.90/1.27    ~v1_funct_1(k5_relat_1(sK1,sK0)) | spl7_4),
% 6.90/1.27    inference(avatar_component_clause,[],[f109])).
% 6.90/1.27  fof(f119,plain,(
% 6.90/1.27    spl7_3),
% 6.90/1.27    inference(avatar_contradiction_clause,[],[f118])).
% 6.90/1.27  fof(f118,plain,(
% 6.90/1.27    $false | spl7_3),
% 6.90/1.27    inference(subsumption_resolution,[],[f117,f29])).
% 6.90/1.27  fof(f117,plain,(
% 6.90/1.27    ~v1_relat_1(sK1) | spl7_3),
% 6.90/1.27    inference(subsumption_resolution,[],[f116,f33])).
% 6.90/1.27  fof(f116,plain,(
% 6.90/1.27    ~v1_relat_1(sK0) | ~v1_relat_1(sK1) | spl7_3),
% 6.90/1.27    inference(resolution,[],[f107,f52])).
% 6.90/1.27  fof(f52,plain,(
% 6.90/1.27    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 6.90/1.27    inference(cnf_transformation,[],[f27])).
% 6.90/1.27  fof(f27,plain,(
% 6.90/1.27    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 6.90/1.27    inference(flattening,[],[f26])).
% 6.90/1.27  fof(f26,plain,(
% 6.90/1.27    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 6.90/1.27    inference(ennf_transformation,[],[f2])).
% 6.90/1.27  fof(f2,axiom,(
% 6.90/1.27    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 6.90/1.27    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 6.90/1.27  fof(f107,plain,(
% 6.90/1.27    ~v1_relat_1(k5_relat_1(sK1,sK0)) | spl7_3),
% 6.90/1.27    inference(avatar_component_clause,[],[f105])).
% 6.90/1.27  fof(f70,plain,(
% 6.90/1.27    ~spl7_1 | ~spl7_2),
% 6.90/1.27    inference(avatar_split_clause,[],[f28,f67,f63])).
% 6.90/1.27  fof(f28,plain,(
% 6.90/1.27    ~v2_funct_1(sK1) | ~v2_funct_1(sK0)),
% 6.90/1.27    inference(cnf_transformation,[],[f13])).
% 6.90/1.27  % SZS output end Proof for theBenchmark
% 6.90/1.27  % (26009)------------------------------
% 6.90/1.27  % (26009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.27  % (26009)Termination reason: Refutation
% 6.90/1.27  
% 6.90/1.27  % (26009)Memory used [KB]: 21108
% 6.90/1.27  % (26009)Time elapsed: 0.846 s
% 6.90/1.27  % (26009)------------------------------
% 6.90/1.27  % (26009)------------------------------
% 6.90/1.27  % (25986)Success in time 0.902 s
%------------------------------------------------------------------------------
