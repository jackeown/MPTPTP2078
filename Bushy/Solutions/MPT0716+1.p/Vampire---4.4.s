%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t171_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:20 EDT 2019

% Result     : Theorem 15.13s
% Output     : Refutation 15.13s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 249 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  304 (1105 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68780,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f98,f99,f752,f67549,f68779])).

fof(f68779,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f68778])).

fof(f68778,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f68770,f67803])).

fof(f67803,plain,
    ( ~ r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f67802,f67561])).

fof(f67561,plain,
    ( r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f81,f1230])).

fof(f1230,plain,
    ( ! [X13] :
        ( r2_hidden(sK6(sK2,X13),k1_relat_1(sK0))
        | r1_tarski(sK2,X13) )
    | ~ spl8_4 ),
    inference(resolution,[],[f756,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',d3_tarski)).

fof(f756,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | r2_hidden(X0,k1_relat_1(sK0)) )
    | ~ spl8_4 ),
    inference(resolution,[],[f97,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f97,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl8_4
  <=> r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f81,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl8_1
  <=> ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f67802,plain,
    ( ~ r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f67801,f48])).

fof(f48,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t171_funct_1)).

fof(f67801,plain,
    ( ~ v1_funct_1(sK0)
    | ~ r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f67800,f47])).

fof(f47,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f67800,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f67799,f46])).

fof(f46,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f67799,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1 ),
    inference(subsumption_resolution,[],[f67795,f45])).

fof(f45,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f67795,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0)
    | ~ r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(sK0))
    | ~ r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1 ),
    inference(resolution,[],[f67566,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',t21_funct_1)).

fof(f67566,plain,
    ( ~ r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68770,plain,
    ( r2_hidden(k1_funct_1(sK0,sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))),k1_relat_1(sK1))
    | ~ spl8_1
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(resolution,[],[f67754,f67565])).

fof(f67565,plain,
    ( r2_hidden(sK6(sK2,k1_relat_1(k5_relat_1(sK0,sK1))),sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f81,f60])).

fof(f67754,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(k1_funct_1(sK0,X3),k1_relat_1(sK1)) )
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f67753,f756])).

fof(f67753,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK0,X3),k1_relat_1(sK1))
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f67752,f48])).

fof(f67752,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK0,X3),k1_relat_1(sK1))
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f67724,f47])).

fof(f67724,plain,
    ( ! [X3] :
        ( r2_hidden(k1_funct_1(sK0,X3),k1_relat_1(sK1))
        | ~ v1_relat_1(sK0)
        | ~ v1_funct_1(sK0)
        | ~ r2_hidden(X3,k1_relat_1(sK0))
        | ~ r2_hidden(X3,sK2) )
    | ~ spl8_2 ),
    inference(resolution,[],[f67583,f75])).

fof(f75,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k1_funct_1(X0,X4),X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X1)
      | k1_funct_1(X0,X4) != X3
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_1__t171_funct_1.p',d12_funct_1)).

fof(f67583,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k9_relat_1(sK0,sK2))
        | r2_hidden(X3,k1_relat_1(sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f90,f59])).

fof(f90,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl8_2
  <=> r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f67549,plain,
    ( ~ spl8_0
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f67548])).

fof(f67548,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f67547,f23962])).

fof(f23962,plain,
    ( r2_hidden(sK4(sK0,sK2,sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_0
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f84,f1922,f59])).

fof(f1922,plain,
    ( r2_hidden(sK4(sK0,sK2,sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),sK2)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f47,f48,f1273,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1273,plain,
    ( r2_hidden(sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k9_relat_1(sK0,sK2))
    | ~ spl8_3 ),
    inference(resolution,[],[f87,f60])).

fof(f87,plain,
    ( ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl8_3
  <=> ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f84,plain,
    ( r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_0 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl8_0
  <=> r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_0])])).

fof(f67547,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f67531,f1274])).

fof(f1274,plain,
    ( ~ r2_hidden(sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ spl8_3 ),
    inference(resolution,[],[f87,f61])).

fof(f67531,plain,
    ( r2_hidden(sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1)),k1_relat_1(sK1))
    | ~ r2_hidden(sK4(sK0,sK2,sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1))),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_3 ),
    inference(superposition,[],[f3182,f1923])).

fof(f1923,plain,
    ( k1_funct_1(sK0,sK4(sK0,sK2,sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1)))) = sK6(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f47,f48,f1273,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3182,plain,(
    ! [X1] :
      ( r2_hidden(k1_funct_1(sK0,X1),k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK0,sK1))) ) ),
    inference(subsumption_resolution,[],[f3180,f47])).

fof(f3180,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK0)
      | r2_hidden(k1_funct_1(sK0,X1),k1_relat_1(sK1))
      | ~ r2_hidden(X1,k1_relat_1(k5_relat_1(sK0,sK1))) ) ),
    inference(resolution,[],[f124,f48])).

fof(f124,plain,(
    ! [X15,X16] :
      ( ~ v1_funct_1(X15)
      | ~ v1_relat_1(X15)
      | r2_hidden(k1_funct_1(X15,X16),k1_relat_1(sK1))
      | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X15,sK1))) ) ),
    inference(subsumption_resolution,[],[f110,f46])).

fof(f110,plain,(
    ! [X15,X16] :
      ( ~ v1_funct_1(sK1)
      | ~ v1_relat_1(X15)
      | ~ v1_funct_1(X15)
      | r2_hidden(k1_funct_1(X15,X16),k1_relat_1(sK1))
      | ~ r2_hidden(X16,k1_relat_1(k5_relat_1(X15,sK1))) ) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f752,plain,
    ( ~ spl8_0
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f751])).

fof(f751,plain,
    ( $false
    | ~ spl8_0
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f744,f666])).

fof(f666,plain,
    ( r2_hidden(sK6(sK2,k1_relat_1(sK0)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_0
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f84,f649,f59])).

fof(f649,plain,
    ( r2_hidden(sK6(sK2,k1_relat_1(sK0)),sK2)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f94,f60])).

fof(f94,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl8_5
  <=> ~ r1_tarski(sK2,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f744,plain,
    ( ~ r2_hidden(sK6(sK2,k1_relat_1(sK0)),k1_relat_1(k5_relat_1(sK0,sK1)))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f46,f45,f48,f47,f650,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f650,plain,
    ( ~ r2_hidden(sK6(sK2,k1_relat_1(sK0)),k1_relat_1(sK0))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f94,f61])).

fof(f99,plain,
    ( ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f42,f93,f86,f80])).

fof(f42,plain,
    ( ~ r1_tarski(sK2,k1_relat_1(sK0))
    | ~ r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | ~ r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f98,plain,
    ( spl8_0
    | spl8_4 ),
    inference(avatar_split_clause,[],[f43,f96,f83])).

fof(f43,plain,
    ( r1_tarski(sK2,k1_relat_1(sK0))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,
    ( spl8_0
    | spl8_2 ),
    inference(avatar_split_clause,[],[f44,f89,f83])).

fof(f44,plain,
    ( r1_tarski(k9_relat_1(sK0,sK2),k1_relat_1(sK1))
    | r1_tarski(sK2,k1_relat_1(k5_relat_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
