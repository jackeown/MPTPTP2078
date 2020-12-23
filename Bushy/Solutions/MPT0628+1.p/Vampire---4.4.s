%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_1__t23_funct_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:22 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 209 expanded)
%              Number of leaves         :    8 (  39 expanded)
%              Depth                    :   20
%              Number of atoms          :  259 ( 981 expanded)
%              Number of equality atoms :   27 ( 147 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f109,f115,f138])).

fof(f138,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f136,f40])).

fof(f40,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) != k1_funct_1(k5_relat_1(X1,X2),X0)
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k1_funct_1(X2,k1_funct_1(X1,X0)) != k1_funct_1(k5_relat_1(X1,X2),X0)
          & r2_hidden(X0,k1_relat_1(X1))
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ( r2_hidden(X0,k1_relat_1(X1))
             => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(X1))
           => k1_funct_1(X2,k1_funct_1(X1,X0)) = k1_funct_1(k5_relat_1(X1,X2),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t23_funct_1.p',t23_funct_1)).

fof(f136,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f135,f121])).

fof(f121,plain,(
    ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f120,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f42,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f45])).

fof(f45,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f118,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f44])).

fof(f44,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f117,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f116,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(sK1))
    | ~ r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          <=> ( r2_hidden(k1_funct_1(X2,X0),k1_relat_1(X1))
              & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t23_funct_1.p',t21_funct_1)).

fof(f77,plain,(
    ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2))) ),
    inference(subsumption_resolution,[],[f76,f40])).

fof(f76,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f75,f45])).

fof(f75,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f74,f44])).

fof(f74,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f73,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(trivial_inequality_removal,[],[f70])).

fof(f70,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_funct_1(sK2,k1_funct_1(sK1,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_funct_1(sK1)
    | ~ r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0)
          | ~ r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( r2_hidden(X0,k1_relat_1(k5_relat_1(X2,X1)))
           => k1_funct_1(X1,k1_funct_1(X2,X0)) = k1_funct_1(k5_relat_1(X2,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t23_funct_1.p',t22_funct_1)).

fof(f43,plain,(
    k1_funct_1(k5_relat_1(sK1,sK2),sK0) != k1_funct_1(sK2,k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f135,plain,
    ( r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f129,f41])).

fof(f129,plain,
    ( ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(sK2)
    | r2_hidden(k1_funct_1(sK1,sK0),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_5 ),
    inference(superposition,[],[f96,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,X1) = k1_xboole_0
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(X1,k1_relat_1(X0))
      | k1_xboole_0 = X2
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t23_funct_1.p',d4_funct_1)).

fof(f96,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_xboole_0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_5
  <=> k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f115,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f113,f44])).

fof(f113,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f112,f41])).

fof(f112,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f111,f40])).

fof(f111,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f110,f45])).

fof(f110,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f90,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_1__t23_funct_1.p',fc2_funct_1)).

fof(f90,plain,
    ( ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_3
  <=> ~ v1_funct_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f109,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f108])).

fof(f108,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f107,f44])).

fof(f107,plain,
    ( ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f106,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f105,f40])).

fof(f105,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f101,f45])).

fof(f101,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f84,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_1
  <=> ~ v1_relat_1(k5_relat_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f99,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f98,f95,f89,f83])).

fof(f98,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_xboole_0
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f72,f77])).

fof(f72,plain,
    ( k1_funct_1(sK2,k1_funct_1(sK1,sK0)) != k1_xboole_0
    | ~ v1_funct_1(k5_relat_1(sK1,sK2))
    | r2_hidden(sK0,k1_relat_1(k5_relat_1(sK1,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK1,sK2)) ),
    inference(superposition,[],[f43,f66])).
%------------------------------------------------------------------------------
