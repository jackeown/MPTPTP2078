%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0623+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 559 expanded)
%              Number of leaves         :   14 ( 144 expanded)
%              Depth                    :   20
%              Number of atoms          :  201 (1954 expanded)
%              Number of equality atoms :   46 ( 671 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f220,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f131,f219])).

fof(f219,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f213])).

fof(f213,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f33,f212])).

fof(f212,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f210,f188])).

fof(f188,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f161,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

fof(f161,plain,
    ( v1_xboole_0(k2_relat_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f138,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f138,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f123,f61])).

fof(f61,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f123,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f50,f110,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f110,plain,(
    ! [X0] : ~ r2_hidden(o_1_0_funct_1(X0),sK0) ),
    inference(backward_demodulation,[],[f78,f108])).

fof(f108,plain,(
    ! [X0] : o_1_0_funct_1(X0) = sK2(k2_relat_1(sK6(X0,sK1)),sK0) ),
    inference(backward_demodulation,[],[f84,f105])).

fof(f105,plain,(
    ! [X0,X1] : o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,sK1),sK4(sK6(X1,sK1),sK2(k2_relat_1(sK6(X1,sK1)),sK0))) ),
    inference(unit_resulting_resolution,[],[f90,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | o_1_0_funct_1(X0) = k1_funct_1(sK6(X0,X1),X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( o_1_0_funct_1(X0) = k1_funct_1(X2,X3)
          | ~ r2_hidden(X3,X1) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => o_1_0_funct_1(X0) = k1_funct_1(X2,X3) )
      & k1_relat_1(X2) = X1
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e1_27_1__funct_1)).

fof(f90,plain,(
    ! [X0] : r2_hidden(sK4(sK6(X0,sK1),sK2(k2_relat_1(sK6(X0,sK1)),sK0)),sK1) ),
    inference(forward_demodulation,[],[f83,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f21])).

fof(f83,plain,(
    ! [X0] : r2_hidden(sK4(sK6(X0,sK1),sK2(k2_relat_1(sK6(X0,sK1)),sK0)),k1_relat_1(sK6(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f42,f43,f77,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | r2_hidden(sK4(X0,X2),k1_relat_1(X0))
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(f77,plain,(
    ! [X0] : r2_hidden(sK2(k2_relat_1(sK6(X0,sK1)),sK0),k2_relat_1(sK6(X0,sK1))) ),
    inference(unit_resulting_resolution,[],[f75,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f75,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK6(X0,sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f42,f43,f44,f28])).

fof(f28,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f43,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f84,plain,(
    ! [X0] : sK2(k2_relat_1(sK6(X0,sK1)),sK0) = k1_funct_1(sK6(X0,sK1),sK4(sK6(X0,sK1),sK2(k2_relat_1(sK6(X0,sK1)),sK0))) ),
    inference(unit_resulting_resolution,[],[f42,f43,f77,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0,X2)) = X2
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,(
    ! [X0] : ~ r2_hidden(sK2(k2_relat_1(sK6(X0,sK1)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f75,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(o_1_0_funct_1(X0),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_1_0_funct_1)).

fof(f210,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f158,f159,f169,f152])).

fof(f152,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),k1_xboole_0)
        | k1_relat_1(X2) != k1_xboole_0
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2) )
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f132,f58])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl7_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f132,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k2_relat_1(X2),k1_xboole_0)
        | ~ v1_funct_1(X2)
        | k1_relat_1(X2) != sK1
        | ~ v1_relat_1(X2) )
    | ~ spl7_2 ),
    inference(backward_demodulation,[],[f28,f61])).

fof(f169,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f160,f48])).

fof(f160,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f138,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f159,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f138,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f158,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f138,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f131,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f64,f50,f110,f49])).

fof(f64,plain,
    ( ~ v1_xboole_0(sK0)
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f62,f48])).

fof(f62,plain,
    ( k1_xboole_0 != sK0
    | spl7_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f63,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f29,f60,f56])).

fof(f29,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
