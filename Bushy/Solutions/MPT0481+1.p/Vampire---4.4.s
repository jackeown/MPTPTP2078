%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t76_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:04 EDT 2019

% Result     : Theorem 131.14s
% Output     : Refutation 131.14s
% Verified   : 
% Statistics : Number of formulae       :  328 (3728 expanded)
%              Number of leaves         :   56 (1032 expanded)
%              Depth                    :   21
%              Number of atoms          : 1936 (15980 expanded)
%              Number of equality atoms :   14 (1238 expanded)
%              Maximal formula depth    :   25 (   9 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9342,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f76,f499,f514,f523,f534,f536,f562,f576,f588,f600,f1249,f2365,f4295,f4299,f4303,f4307,f4311,f4338,f4342,f4459,f4463,f7118,f7119,f7120,f7121,f7122,f7123,f7131,f7140,f7144,f8594,f8598,f8602,f8609,f8613,f8614,f8627,f8643,f8647,f8761,f8765,f8790,f8794,f8823,f8824,f8828,f8832,f8836,f8997,f8998,f8999,f9000,f9001,f9028,f9032,f9053,f9057,f9207,f9211,f9324,f9325,f9326,f9327,f9328,f9329])).

fof(f9329,plain,
    ( ~ spl11_9
    | ~ spl11_11
    | ~ spl11_1
    | spl11_5 ),
    inference(avatar_split_clause,[],[f9294,f74,f58,f512,f497])).

fof(f497,plain,
    ( spl11_9
  <=> ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f512,plain,
    ( spl11_11
  <=> ~ v1_relat_1(k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_11])])).

fof(f58,plain,
    ( spl11_1
  <=> ~ v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f74,plain,
    ( spl11_5
  <=> ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f9294,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl11_5 ),
    inference(resolution,[],[f8736,f75])).

fof(f75,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f8736,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f8648])).

fof(f8648,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)
      | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | ~ v1_relat_1(k5_relat_1(X1,k6_relat_1(X0)))
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(resolution,[],[f271,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t76_relat_1.p',d3_relat_1)).

fof(f271,plain,(
    ! [X26,X24,X25] :
      ( r2_hidden(k4_tarski(sK2(k5_relat_1(X24,k6_relat_1(X25)),X26),sK3(k5_relat_1(X24,k6_relat_1(X25)),X26)),X24)
      | ~ v1_relat_1(k6_relat_1(X25))
      | ~ v1_relat_1(X24)
      | r1_tarski(k5_relat_1(X24,k6_relat_1(X25)),X26)
      | ~ v1_relat_1(k5_relat_1(X24,k6_relat_1(X25))) ) ),
    inference(resolution,[],[f108,f193])).

fof(f193,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ sP6(X11,X10,k6_relat_1(X9),X8)
      | r2_hidden(k4_tarski(X10,X11),X8) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X10,X8,X11,X9] :
      ( r2_hidden(k4_tarski(X10,X11),X8)
      | ~ sP6(X11,X10,k6_relat_1(X9),X8)
      | ~ sP6(X11,X10,k6_relat_1(X9),X8) ) ),
    inference(superposition,[],[f38,f146])).

fof(f146,plain,(
    ! [X2,X0,X3,X1] :
      ( sK7(X3,k6_relat_1(X2),X1,X0) = X0
      | ~ sP6(X0,X1,k6_relat_1(X2),X3) ) ),
    inference(resolution,[],[f91,f46])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ~ sP10(X3,X2,X0)
      | X2 = X3 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k6_relat_1(X0) = X1
      <=> ! [X2,X3] :
            ( r2_hidden(k4_tarski(X2,X3),X1)
          <=> ( X2 = X3
              & r2_hidden(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t76_relat_1.p',d10_relat_1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,sK7(X3,k6_relat_1(X2),X1,X0),X2)
      | ~ sP6(X0,X1,k6_relat_1(X2),X3) ) ),
    inference(global_subsumption,[],[f51,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X0,X1,k6_relat_1(X2),X3)
      | sP10(X0,sK7(X3,k6_relat_1(X2),X1,X0),X2)
      | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    inference(resolution,[],[f39,f54])).

fof(f54,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | sP10(X3,X2,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | sP10(X3,X2,X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f39,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X3,X4),X4),X1)
      | ~ sP6(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k5_relat_1(X0,X1) = X2
              <=> ! [X3,X4] :
                    ( r2_hidden(k4_tarski(X3,X4),X2)
                  <=> ? [X5] :
                        ( r2_hidden(k4_tarski(X5,X4),X1)
                        & r2_hidden(k4_tarski(X3,X5),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t76_relat_1.p',d8_relat_1)).

fof(f51,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t76_relat_1.p',dt_k6_relat_1)).

fof(f38,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,sK7(X0,X1,X3,X4)),X0)
      | ~ sP6(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP6(sK3(k5_relat_1(X1,X0),X2),sK2(k5_relat_1(X1,X0),X2),X0,X1)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,X0),X2) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | sP6(sK3(k5_relat_1(X1,X0),X2),sK2(k5_relat_1(X1,X0),X2),X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k5_relat_1(X1,X0),X2) ) ),
    inference(resolution,[],[f52,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | sP6(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | sP6(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9328,plain,
    ( ~ spl11_61
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_1
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f9319,f491,f58,f512,f497,f8607])).

fof(f8607,plain,
    ( spl11_61
  <=> ~ r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_61])])).

fof(f491,plain,
    ( spl11_6
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f9319,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f9291])).

fof(f9291,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ r1_tarski(sK1,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl11_6 ),
    inference(resolution,[],[f8736,f492])).

fof(f492,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X0)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f491])).

fof(f9327,plain,
    ( spl11_58
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_1
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f9320,f7129,f58,f512,f497,f8600])).

fof(f8600,plain,
    ( spl11_58
  <=> ! [X5] :
        ( ~ r1_tarski(X5,sK1)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(sK1,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_58])])).

fof(f7129,plain,
    ( spl11_48
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X1)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f9320,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X9,sK1)
        | ~ r1_tarski(sK1,X9) )
    | ~ spl11_48 ),
    inference(duplicate_literal_removal,[],[f9290])).

fof(f9290,plain,
    ( ! [X9] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X9,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X9) )
    | ~ spl11_48 ),
    inference(resolution,[],[f8736,f7130])).

fof(f7130,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f7129])).

fof(f9326,plain,
    ( spl11_56
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_1
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f9321,f7138,f58,f512,f497,f8596])).

fof(f8596,plain,
    ( spl11_56
  <=> ! [X3,X4] :
        ( ~ r1_tarski(X3,sK1)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(sK1,X4)
        | ~ r1_tarski(X4,X3)
        | ~ v1_relat_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_56])])).

fof(f7138,plain,
    ( spl11_50
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_50])])).

fof(f9321,plain,
    ( ! [X8,X7] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X7,sK1)
        | ~ r1_tarski(sK1,X8)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X7)
        | ~ v1_relat_1(X7) )
    | ~ spl11_50 ),
    inference(duplicate_literal_removal,[],[f9289])).

fof(f9289,plain,
    ( ! [X8,X7] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X7,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X8)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X7)
        | ~ v1_relat_1(X7) )
    | ~ spl11_50 ),
    inference(resolution,[],[f8736,f7139])).

fof(f7139,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X2)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_50 ),
    inference(avatar_component_clause,[],[f7138])).

fof(f9325,plain,
    ( spl11_54
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_1
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f9322,f8641,f58,f512,f497,f8592])).

fof(f8592,plain,
    ( spl11_54
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(sK1,X1)
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_54])])).

fof(f8641,plain,
    ( spl11_64
  <=> ! [X1,X3,X2,X4] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_64])])).

fof(f9322,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(sK1,X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X4)
        | ~ r1_tarski(X4,sK1) )
    | ~ spl11_64 ),
    inference(duplicate_literal_removal,[],[f9288])).

fof(f9288,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X4)
        | ~ r1_tarski(X4,sK1) )
    | ~ spl11_64 ),
    inference(resolution,[],[f8736,f8642])).

fof(f8642,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X4)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X1,sK1) )
    | ~ spl11_64 ),
    inference(avatar_component_clause,[],[f8641])).

fof(f9324,plain,
    ( spl11_62
    | ~ spl11_9
    | ~ spl11_11
    | ~ spl11_1
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f9323,f8759,f58,f512,f497,f8611])).

fof(f8611,plain,
    ( spl11_62
  <=> ! [X9,X7,X8,X6] :
        ( ~ r1_tarski(X6,sK1)
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X9,X8)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X6)
        | ~ r1_tarski(sK1,X7)
        | ~ r1_tarski(X7,X9)
        | ~ v1_relat_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_62])])).

fof(f8759,plain,
    ( spl11_68
  <=> ! [X3,X5,X2,X4,X6] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X4,X2)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_68])])).

fof(f9323,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK1,X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X3,X0)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl11_68 ),
    inference(duplicate_literal_removal,[],[f9287])).

fof(f9287,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X3,X0)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X2,X3) )
    | ~ spl11_68 ),
    inference(resolution,[],[f8736,f8760])).

fof(f8760,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X6)
        | ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X4,X2)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X3,X4) )
    | ~ spl11_68 ),
    inference(avatar_component_clause,[],[f8759])).

fof(f9211,plain,
    ( ~ spl11_9
    | spl11_94
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f9202,f8759,f9209,f497])).

fof(f9209,plain,
    ( spl11_94
  <=> ! [X18,X20,X17,X19,X21] :
        ( ~ r1_tarski(X17,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X18))
        | ~ v1_relat_1(k6_relat_1(X18))
        | ~ v1_relat_1(X21)
        | ~ r1_tarski(X21,X17)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X18),k6_relat_1(X18)))
        | ~ r1_tarski(X20,X21)
        | ~ v1_relat_1(X20)
        | ~ r1_tarski(X19,X20)
        | ~ v1_relat_1(X19)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X18),k6_relat_1(X18)),X19) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_94])])).

fof(f9202,plain,
    ( ! [X21,X19,X17,X20,X18] :
        ( ~ r1_tarski(X17,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X18),k6_relat_1(X18)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X18),k6_relat_1(X18)),X19)
        | ~ v1_relat_1(X19)
        | ~ r1_tarski(X19,X20)
        | ~ v1_relat_1(X17)
        | ~ v1_relat_1(X20)
        | ~ r1_tarski(X21,X17)
        | ~ v1_relat_1(X21)
        | ~ r1_tarski(X20,X21)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(k6_relat_1(X18))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X18)) )
    | ~ spl11_68 ),
    inference(resolution,[],[f8760,f4150])).

fof(f4150,plain,(
    ! [X6,X7] :
      ( r1_tarski(X6,k5_relat_1(k6_relat_1(X7),k6_relat_1(X7)))
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(k6_relat_1(X7))
      | ~ r1_tarski(X6,k6_relat_1(X7)) ) ),
    inference(resolution,[],[f4145,f390])).

fof(f390,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ v1_relat_1(X4)
      | r1_tarski(X4,X3)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ r1_tarski(X4,k6_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f387])).

fof(f387,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ v1_relat_1(X4)
      | r1_tarski(X4,X3)
      | ~ v1_relat_1(k6_relat_1(X2))
      | ~ r1_tarski(X4,k6_relat_1(X2))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X2))
      | r1_tarski(X4,X3) ) ),
    inference(resolution,[],[f182,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( sP10(sK3(X0,X2),sK2(X0,X2),X1)
      | ~ r1_tarski(X0,k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | r1_tarski(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,k6_relat_1(X1))
      | sP10(sK3(X0,X2),sK2(X0,X2),X1)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f94,f34])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,k6_relat_1(X3))
      | sP10(X1,X0,X3)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f33,f54])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f182,plain,(
    ! [X6,X8,X7] :
      ( ~ sP10(sK3(X8,X7),sK2(X8,X7),X6)
      | ~ r1_tarski(k6_relat_1(X6),X7)
      | ~ v1_relat_1(X8)
      | r1_tarski(X8,X7)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_relat_1(k6_relat_1(X6))
      | ~ r1_tarski(k6_relat_1(X6),X7)
      | ~ v1_relat_1(X8)
      | r1_tarski(X8,X7)
      | ~ sP10(sK3(X8,X7),sK2(X8,X7),X6)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(resolution,[],[f95,f55])).

fof(f55,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(k4_tarski(X2,X3),k6_relat_1(X0))
      | ~ sP10(X3,X2,X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ sP10(X3,X2,X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | k6_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK2(X4,X5),sK3(X4,X5)),X6)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(X6,X5)
      | ~ v1_relat_1(X4)
      | r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f33,f35])).

fof(f4145,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ),
    inference(global_subsumption,[],[f51,f4144])).

fof(f4144,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f4128])).

fof(f4128,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
      | r1_tarski(k6_relat_1(X0),k5_relat_1(k6_relat_1(X0),k6_relat_1(X0))) ) ),
    inference(resolution,[],[f1055,f1125])).

fof(f1125,plain,(
    ! [X26,X27] :
      ( sP10(sK3(k6_relat_1(X26),X27),sK3(k6_relat_1(X26),X27),X26)
      | r1_tarski(k6_relat_1(X26),X27) ) ),
    inference(duplicate_literal_removal,[],[f1120])).

fof(f1120,plain,(
    ! [X26,X27] :
      ( sP10(sK3(k6_relat_1(X26),X27),sK3(k6_relat_1(X26),X27),X26)
      | r1_tarski(k6_relat_1(X26),X27)
      | r1_tarski(k6_relat_1(X26),X27) ) ),
    inference(resolution,[],[f741,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( sP10(sK3(k6_relat_1(X0),X1),sK2(k6_relat_1(X0),X1),X0)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(global_subsumption,[],[f51,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k6_relat_1(X0),X1)
      | sP10(sK3(k6_relat_1(X0),X1),sK2(k6_relat_1(X0),X1),X0) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k6_relat_1(X0))
      | r1_tarski(k6_relat_1(X0),X1)
      | sP10(sK3(k6_relat_1(X0),X1),sK2(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f34,f54])).

fof(f741,plain,(
    ! [X33,X31,X34,X32] :
      ( ~ sP10(X31,sK2(k6_relat_1(X33),X34),X32)
      | sP10(X31,X31,X32)
      | r1_tarski(k6_relat_1(X33),X34) ) ),
    inference(resolution,[],[f731,f103])).

fof(f103,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK2(k6_relat_1(X4),X5),sK2(k6_relat_1(X4),X5)),k6_relat_1(X4))
      | r1_tarski(k6_relat_1(X4),X5) ) ),
    inference(global_subsumption,[],[f51,f99])).

fof(f99,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK2(k6_relat_1(X4),X5),sK2(k6_relat_1(X4),X5)),k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X4))
      | r1_tarski(k6_relat_1(X4),X5) ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X4,X5] :
      ( r2_hidden(k4_tarski(sK2(k6_relat_1(X4),X5),sK2(k6_relat_1(X4),X5)),k6_relat_1(X4))
      | ~ v1_relat_1(k6_relat_1(X4))
      | r1_tarski(k6_relat_1(X4),X5)
      | r1_tarski(k6_relat_1(X4),X5) ) ),
    inference(superposition,[],[f34,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK2(k6_relat_1(X0),X1) = sK3(k6_relat_1(X0),X1)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f84,f46])).

fof(f731,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X4)
      | sP10(X0,X0,X1)
      | ~ sP10(X0,X3,X1) ) ),
    inference(global_subsumption,[],[f51,f724])).

fof(f724,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP10(X0,X0,X1)
      | ~ r2_hidden(k4_tarski(X2,X3),X4)
      | ~ sP10(X0,X3,X1)
      | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    inference(resolution,[],[f206,f55])).

fof(f206,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ r2_hidden(k4_tarski(X7,X5),k6_relat_1(X6))
      | sP10(X5,X5,X6)
      | ~ r2_hidden(k4_tarski(X8,X7),X9) ) ),
    inference(resolution,[],[f195,f37])).

fof(f37,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( sP6(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X5,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X5),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f195,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X2,k6_relat_1(X1),X0)
      | sP10(X3,X3,X1) ) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X3,X3,X1)
      | ~ sP6(X3,X2,k6_relat_1(X1),X0)
      | ~ sP6(X3,X2,k6_relat_1(X1),X0) ) ),
    inference(superposition,[],[f91,f146])).

fof(f1055,plain,(
    ! [X4,X3] :
      ( ~ sP10(sK3(X3,k5_relat_1(X3,k6_relat_1(X4))),sK3(X3,k5_relat_1(X3,k6_relat_1(X4))),X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X4))
      | r1_tarski(X3,k5_relat_1(X3,k6_relat_1(X4))) ) ),
    inference(duplicate_literal_removal,[],[f1048])).

fof(f1048,plain,(
    ! [X4,X3] :
      ( r1_tarski(X3,k5_relat_1(X3,k6_relat_1(X4)))
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(k6_relat_1(X4))
      | ~ sP10(sK3(X3,k5_relat_1(X3,k6_relat_1(X4))),sK3(X3,k5_relat_1(X3,k6_relat_1(X4))),X4)
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(resolution,[],[f544,f55])).

fof(f544,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,k5_relat_1(X0,X1)),sK3(X0,k5_relat_1(X0,X1))),X1)
      | r1_tarski(X0,k5_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(duplicate_literal_removal,[],[f537])).

fof(f537,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,k5_relat_1(X0,X1))
      | ~ r2_hidden(k4_tarski(sK3(X0,k5_relat_1(X0,X1)),sK3(X0,k5_relat_1(X0,X1))),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f290,f34])).

fof(f290,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_hidden(k4_tarski(sK2(X8,k5_relat_1(X6,X7)),X9),X6)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X8)
      | r1_tarski(X8,k5_relat_1(X6,X7))
      | ~ r2_hidden(k4_tarski(X9,sK3(X8,k5_relat_1(X6,X7))),X7)
      | ~ v1_relat_1(X7) ) ),
    inference(global_subsumption,[],[f36,f285])).

fof(f285,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ v1_relat_1(k5_relat_1(X6,X7))
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6)
      | ~ v1_relat_1(X8)
      | r1_tarski(X8,k5_relat_1(X6,X7))
      | ~ r2_hidden(k4_tarski(X9,sK3(X8,k5_relat_1(X6,X7))),X7)
      | ~ r2_hidden(k4_tarski(sK2(X8,k5_relat_1(X6,X7)),X9),X6) ) ),
    inference(resolution,[],[f112,f37])).

fof(f112,plain,(
    ! [X6,X4,X5] :
      ( ~ sP6(sK3(X6,k5_relat_1(X5,X4)),sK2(X6,k5_relat_1(X5,X4)),X4,X5)
      | ~ v1_relat_1(k5_relat_1(X5,X4))
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(X5)
      | ~ v1_relat_1(X6)
      | r1_tarski(X6,k5_relat_1(X5,X4)) ) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X4,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X3,X4),k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k5_relat_1(X0,X1))
      | ~ sP6(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ sP6(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k5_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t76_relat_1.p',dt_k5_relat_1)).

fof(f9207,plain,
    ( ~ spl11_9
    | spl11_92
    | ~ spl11_68 ),
    inference(avatar_split_clause,[],[f9200,f8759,f9205,f497])).

fof(f9205,plain,
    ( spl11_92
  <=> ! [X9,X5,X7,X8,X10,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X10)
        | ~ v1_relat_1(X10)
        | ~ r1_tarski(X10,X9)
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X9,X5)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X4)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X7,X8)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X6,X7)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X5,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f9200,plain,
    ( ! [X6,X4,X10,X8,X7,X5,X9] :
        ( ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X7)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X8,X4)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X7,X8)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X10)
        | ~ r1_tarski(X10,X9)
        | ~ r1_tarski(X9,X5)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X10) )
    | ~ spl11_68 ),
    inference(resolution,[],[f8760,f1544])).

fof(f1544,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X3) ) ),
    inference(duplicate_literal_removal,[],[f1533])).

fof(f1533,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ r1_tarski(X3,X2)
      | ~ r1_tarski(X2,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X3)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f479,f34])).

fof(f479,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK2(X5,X4),sK3(X5,X4)),X7)
      | ~ v1_relat_1(X5)
      | r1_tarski(X5,X4)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X6)
      | ~ r1_tarski(X6,X3)
      | ~ r1_tarski(X3,X4)
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X7,X6) ) ),
    inference(resolution,[],[f176,f33])).

fof(f176,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r2_hidden(k4_tarski(sK2(X4,X3),sK3(X4,X3)),X5)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X4)
      | r1_tarski(X4,X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X5)
      | ~ r1_tarski(X5,X2) ) ),
    inference(resolution,[],[f95,f33])).

fof(f9057,plain,
    ( ~ spl11_9
    | spl11_90
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f9049,f8645,f9055,f497])).

fof(f9055,plain,
    ( spl11_90
  <=> ! [X5,X4,X6] :
        ( ~ v1_relat_1(X4)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,k6_relat_1(X5))
        | ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X4)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_90])])).

fof(f8645,plain,
    ( spl11_66
  <=> ! [X9,X8] :
        ( ~ v1_relat_1(X8)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X9))
        | ~ v1_relat_1(k6_relat_1(X9))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)),X8)
        | ~ r1_tarski(X8,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_66])])).

fof(f9049,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X4)
        | ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X6,k6_relat_1(X5))
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X6) )
    | ~ spl11_66 ),
    inference(resolution,[],[f8646,f486])).

fof(f486,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X1)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f478])).

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X2,X0)
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X1) ) ),
    inference(resolution,[],[f176,f34])).

fof(f8646,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X9))
        | ~ v1_relat_1(X8)
        | ~ v1_relat_1(k6_relat_1(X9))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)),X8)
        | ~ r1_tarski(X8,sK1) )
    | ~ spl11_66 ),
    inference(avatar_component_clause,[],[f8645])).

fof(f9053,plain,
    ( ~ spl11_9
    | spl11_88
    | ~ spl11_66 ),
    inference(avatar_split_clause,[],[f9048,f8645,f9051,f497])).

fof(f9051,plain,
    ( spl11_88
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,k6_relat_1(X1))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)),X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_88])])).

fof(f9048,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)),X0)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X2,k6_relat_1(X1))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X3) )
    | ~ spl11_66 ),
    inference(resolution,[],[f8646,f1544])).

fof(f9032,plain,
    ( ~ spl11_9
    | spl11_86
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f9023,f8641,f9030,f497])).

fof(f9030,plain,
    ( spl11_86
  <=> ! [X16,X15,X17,X14] :
        ( ~ v1_relat_1(X14)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X15))
        | ~ v1_relat_1(k6_relat_1(X15))
        | ~ r1_tarski(X14,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X15)))
        | ~ r1_tarski(X17,X14)
        | ~ v1_relat_1(X17)
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X16)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X15),k6_relat_1(X15)),X16) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_86])])).

fof(f9023,plain,
    ( ! [X14,X17,X15,X16] :
        ( ~ v1_relat_1(X14)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X15),k6_relat_1(X15)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X15),k6_relat_1(X15)),X16)
        | ~ v1_relat_1(X16)
        | ~ r1_tarski(X16,X17)
        | ~ v1_relat_1(X17)
        | ~ r1_tarski(X17,X14)
        | ~ r1_tarski(X14,sK1)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(k6_relat_1(X15))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X15)) )
    | ~ spl11_64 ),
    inference(resolution,[],[f8642,f4150])).

fof(f9028,plain,
    ( ~ spl11_9
    | spl11_84
    | ~ spl11_64 ),
    inference(avatar_split_clause,[],[f9021,f8641,f9026,f497])).

fof(f9026,plain,
    ( spl11_84
  <=> ! [X3,X5,X7,X8,X4,X6] :
        ( ~ v1_relat_1(X3)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X8)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X7)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X7,X4)
        | ~ r1_tarski(X3,sK1)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X6,X3)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_84])])).

fof(f9021,plain,
    ( ! [X6,X4,X8,X7,X5,X3] :
        ( ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X3)
        | ~ r1_tarski(X3,sK1)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X7)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X7)
        | ~ r1_tarski(X7,X4)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X8) )
    | ~ spl11_64 ),
    inference(resolution,[],[f8642,f1544])).

fof(f9001,plain,
    ( ~ spl11_15
    | spl11_82
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f8994,f4340,f8834,f532])).

fof(f532,plain,
    ( spl11_15
  <=> ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f8834,plain,
    ( spl11_82
  <=> ! [X11,X10] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),k6_relat_1(X10)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X11))
        | ~ v1_relat_1(k6_relat_1(X11))
        | ~ r1_tarski(k6_relat_1(X10),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X11),k6_relat_1(X11)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X11),k6_relat_1(X11)),k6_relat_1(X10))
        | ~ v1_relat_1(k6_relat_1(X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_82])])).

fof(f4340,plain,
    ( spl11_40
  <=> ! [X3,X4] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(k6_relat_1(X3))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_40])])).

fof(f8994,plain,
    ( ! [X10,X11] :
        ( ~ r1_tarski(k6_relat_1(X10),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),k6_relat_1(X10)))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X11),k6_relat_1(X11)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X11),k6_relat_1(X11)),k6_relat_1(X10))
        | ~ v1_relat_1(k6_relat_1(X10))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X11))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X11)) )
    | ~ spl11_40 ),
    inference(resolution,[],[f7847,f4150])).

fof(f7847,plain,
    ( ! [X14,X13] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X14)
        | ~ r1_tarski(k6_relat_1(X13),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X13),k6_relat_1(X13)))
        | ~ v1_relat_1(X14)
        | ~ r1_tarski(X14,k6_relat_1(X13))
        | ~ v1_relat_1(k6_relat_1(X13)) )
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f7826])).

fof(f7826,plain,
    ( ! [X14,X13] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X13),k6_relat_1(X13)))
        | ~ r1_tarski(k6_relat_1(X13),sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X14)
        | ~ v1_relat_1(X14)
        | ~ r1_tarski(X14,k6_relat_1(X13))
        | ~ v1_relat_1(k6_relat_1(X13))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X13),k6_relat_1(X13))) )
    | ~ spl11_40 ),
    inference(resolution,[],[f6685,f4341])).

fof(f4341,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)),sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(k6_relat_1(X3))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3))) )
    | ~ spl11_40 ),
    inference(avatar_component_clause,[],[f4340])).

fof(f6685,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)),X8)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)))
      | ~ r1_tarski(k6_relat_1(X6),X8) ) ),
    inference(global_subsumption,[],[f51,f6681])).

fof(f6681,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)),X8)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)))
      | ~ r1_tarski(k6_relat_1(X6),X8)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(duplicate_literal_removal,[],[f6644])).

fof(f6644,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)),X8)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)))
      | ~ r1_tarski(k6_relat_1(X6),X8)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)))
      | r1_tarski(k5_relat_1(k6_relat_1(X6),k6_relat_1(X7)),X8)
      | ~ v1_relat_1(k6_relat_1(X6)) ) ),
    inference(resolution,[],[f274,f182])).

fof(f274,plain,(
    ! [X14,X12,X13] :
      ( sP10(sK3(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14),sK2(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14),X12)
      | r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13))) ) ),
    inference(global_subsumption,[],[f51,f273])).

fof(f273,plain,(
    ! [X14,X12,X13] :
      ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)))
      | ~ v1_relat_1(k6_relat_1(X13))
      | r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14)
      | sP10(sK3(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14),sK2(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14),X12) ) ),
    inference(global_subsumption,[],[f51,f267])).

fof(f267,plain,(
    ! [X14,X12,X13] :
      ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)))
      | ~ v1_relat_1(k6_relat_1(X13))
      | ~ v1_relat_1(k6_relat_1(X12))
      | r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14)
      | sP10(sK3(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14),sK2(k5_relat_1(k6_relat_1(X12),k6_relat_1(X13)),X14),X12) ) ),
    inference(resolution,[],[f108,f191])).

fof(f191,plain,(
    ! [X19,X17,X18,X16] :
      ( ~ sP6(X19,X18,k6_relat_1(X17),k6_relat_1(X16))
      | sP10(X19,X18,X16) ) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X19,X17,X18,X16] :
      ( sP10(X19,X18,X16)
      | ~ sP6(X19,X18,k6_relat_1(X17),k6_relat_1(X16))
      | ~ sP6(X19,X18,k6_relat_1(X17),k6_relat_1(X16)) ) ),
    inference(superposition,[],[f89,f146])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(sK7(k6_relat_1(X3),X2,X1,X0),X1,X3)
      | ~ sP6(X0,X1,X2,k6_relat_1(X3)) ) ),
    inference(global_subsumption,[],[f51,f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X0,X1,X2,k6_relat_1(X3))
      | sP10(sK7(k6_relat_1(X3),X2,X1,X0),X1,X3)
      | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    inference(resolution,[],[f38,f54])).

fof(f9000,plain,
    ( ~ spl11_15
    | spl11_80
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f8992,f4340,f8830,f532])).

fof(f8830,plain,
    ( spl11_80
  <=> ! [X3,X5,X4,X6] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X4)
        | ~ r1_tarski(k6_relat_1(X3),sK1)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_80])])).

fof(f8992,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ r1_tarski(k6_relat_1(X3),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(k6_relat_1(X3))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X5)
        | ~ r1_tarski(X5,X4)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X6) )
    | ~ spl11_40 ),
    inference(resolution,[],[f7847,f1544])).

fof(f8999,plain,
    ( ~ spl11_15
    | spl11_78
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f8995,f4340,f8826,f532])).

fof(f8826,plain,
    ( spl11_78
  <=> ! [X2] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ r1_tarski(k6_relat_1(X2),sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_78])])).

fof(f8995,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X2)) )
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f8991])).

fof(f8991,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k6_relat_1(X2),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_40 ),
    inference(resolution,[],[f7847,f87])).

fof(f87,plain,(
    ! [X2] :
      ( r1_tarski(X2,X2)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(X2,X2)
      | ~ v1_relat_1(X2)
      | r1_tarski(X2,X2) ) ),
    inference(resolution,[],[f35,f34])).

fof(f8998,plain,
    ( ~ spl11_15
    | ~ spl11_11
    | ~ spl11_1
    | spl11_76
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f8996,f4340,f8821,f58,f512,f532])).

fof(f8821,plain,
    ( spl11_76
  <=> ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ r1_tarski(k6_relat_1(X0),sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f8996,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k6_relat_1(X1),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_40 ),
    inference(duplicate_literal_removal,[],[f8990])).

fof(f8990,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k6_relat_1(X1),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_40 ),
    inference(resolution,[],[f7847,f8515])).

fof(f8515,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X0)) ) ),
    inference(duplicate_literal_removal,[],[f8427])).

fof(f8427,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(k6_relat_1(X1))
      | r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X0)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X0))
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),X0))
      | r1_tarski(k5_relat_1(k6_relat_1(X1),X0),X0) ) ),
    inference(resolution,[],[f264,f35])).

fof(f264,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(k4_tarski(sK2(k5_relat_1(k6_relat_1(X3),X4),X5),sK3(k5_relat_1(k6_relat_1(X3),X4),X5)),X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(k6_relat_1(X3))
      | r1_tarski(k5_relat_1(k6_relat_1(X3),X4),X5)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),X4)) ) ),
    inference(resolution,[],[f108,f136])).

fof(f136,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP6(X7,X6,X5,k6_relat_1(X4))
      | r2_hidden(k4_tarski(X6,X7),X5) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
    ! [X6,X4,X7,X5] :
      ( r2_hidden(k4_tarski(X6,X7),X5)
      | ~ sP6(X7,X6,X5,k6_relat_1(X4))
      | ~ sP6(X7,X6,X5,k6_relat_1(X4)) ) ),
    inference(superposition,[],[f39,f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( sK7(k6_relat_1(X3),X2,X1,X0) = X1
      | ~ sP6(X0,X1,X2,k6_relat_1(X3)) ) ),
    inference(resolution,[],[f89,f46])).

fof(f8997,plain,
    ( ~ spl11_1
    | spl11_76
    | ~ spl11_2
    | ~ spl11_40 ),
    inference(avatar_split_clause,[],[f8989,f4340,f65,f8821,f58])).

fof(f65,plain,
    ( spl11_2
  <=> r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f8989,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k6_relat_1(X0),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0)) )
    | ~ spl11_2
    | ~ spl11_40 ),
    inference(resolution,[],[f7847,f66])).

fof(f66,plain,
    ( r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f8836,plain,
    ( ~ spl11_15
    | spl11_82
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f8817,f4461,f8834,f532])).

fof(f4461,plain,
    ( spl11_44
  <=> ! [X5,X4,X6] :
        ( ~ v1_relat_1(X4)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,k6_relat_1(X5))
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_44])])).

fof(f8817,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),k6_relat_1(X10)))
        | ~ v1_relat_1(k6_relat_1(X10))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X11),k6_relat_1(X11)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X11),k6_relat_1(X11)),k6_relat_1(X10))
        | ~ r1_tarski(k6_relat_1(X10),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X11))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X11)) )
    | ~ spl11_44 ),
    inference(resolution,[],[f8585,f4150])).

fof(f8585,plain,
    ( ! [X10,X11] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X11)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),k6_relat_1(X10)))
        | ~ v1_relat_1(k6_relat_1(X10))
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(X11,k6_relat_1(X10))
        | ~ r1_tarski(k6_relat_1(X10),sK1) )
    | ~ spl11_44 ),
    inference(duplicate_literal_removal,[],[f8559])).

fof(f8559,plain,
    ( ! [X10,X11] :
        ( ~ v1_relat_1(k6_relat_1(X10))
        | ~ v1_relat_1(k6_relat_1(X10))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),k6_relat_1(X10)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X11)
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(X11,k6_relat_1(X10))
        | ~ v1_relat_1(k6_relat_1(X10))
        | ~ r1_tarski(k6_relat_1(X10),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X10),k6_relat_1(X10)))
        | ~ v1_relat_1(k6_relat_1(X10)) )
    | ~ spl11_44 ),
    inference(resolution,[],[f8515,f4462])).

fof(f4462,plain,
    ( ! [X6,X4,X5] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X4)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,k6_relat_1(X5))
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ v1_relat_1(X4) )
    | ~ spl11_44 ),
    inference(avatar_component_clause,[],[f4461])).

fof(f8832,plain,
    ( ~ spl11_15
    | spl11_80
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f8815,f4461,f8830,f532])).

fof(f8815,plain,
    ( ! [X6,X4,X5,X3] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ v1_relat_1(k6_relat_1(X3))
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ r1_tarski(k6_relat_1(X3),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X5)
        | ~ r1_tarski(X5,X4)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X6) )
    | ~ spl11_44 ),
    inference(resolution,[],[f8585,f1544])).

fof(f8828,plain,
    ( ~ spl11_15
    | spl11_78
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f8818,f4461,f8826,f532])).

fof(f8818,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X2))
        | ~ r1_tarski(k6_relat_1(X2),sK1) )
    | ~ spl11_44 ),
    inference(duplicate_literal_removal,[],[f8814])).

fof(f8814,plain,
    ( ! [X2] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X2))
        | ~ r1_tarski(k6_relat_1(X2),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_44 ),
    inference(resolution,[],[f8585,f87])).

fof(f8824,plain,
    ( ~ spl11_15
    | ~ spl11_11
    | ~ spl11_1
    | spl11_76
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f8819,f4461,f8821,f58,f512,f532])).

fof(f8819,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X1),sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_44 ),
    inference(duplicate_literal_removal,[],[f8813])).

fof(f8813,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X1))
        | ~ r1_tarski(k6_relat_1(X1),sK1)
        | ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_44 ),
    inference(resolution,[],[f8585,f8515])).

fof(f8823,plain,
    ( ~ spl11_1
    | spl11_76
    | ~ spl11_2
    | ~ spl11_44 ),
    inference(avatar_split_clause,[],[f8812,f4461,f65,f8821,f58])).

fof(f8812,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,k6_relat_1(X0))
        | ~ r1_tarski(k6_relat_1(X0),sK1) )
    | ~ spl11_2
    | ~ spl11_44 ),
    inference(resolution,[],[f8585,f66])).

fof(f8794,plain,
    ( ~ spl11_9
    | spl11_74
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f8786,f7142,f8792,f497])).

fof(f8792,plain,
    ( spl11_74
  <=> ! [X3,X4] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)),sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ v1_relat_1(k6_relat_1(X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_74])])).

fof(f7142,plain,
    ( spl11_52
  <=> ! [X5] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X5))
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_52])])).

fof(f8786,plain,
    ( ! [X4,X3] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)),sK1)
        | ~ v1_relat_1(k6_relat_1(X3))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X4) )
    | ~ spl11_52 ),
    inference(resolution,[],[f7143,f486])).

fof(f7143,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X5))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),sK1)
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5))) )
    | ~ spl11_52 ),
    inference(avatar_component_clause,[],[f7142])).

fof(f8790,plain,
    ( ~ spl11_9
    | spl11_72
    | ~ spl11_52 ),
    inference(avatar_split_clause,[],[f8785,f7142,f8788,f497])).

fof(f8788,plain,
    ( spl11_72
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)),sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_72])])).

fof(f8785,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)),sK1)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X2) )
    | ~ spl11_52 ),
    inference(resolution,[],[f7143,f1544])).

fof(f8765,plain,
    ( ~ spl11_9
    | spl11_70
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f8756,f7138,f8763,f497])).

fof(f8763,plain,
    ( spl11_70
  <=> ! [X11,X13,X12] :
        ( ~ r1_tarski(X11,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X12))
        | ~ v1_relat_1(k6_relat_1(X12))
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)))
        | ~ r1_tarski(X13,X11)
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)),X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f8756,plain,
    ( ! [X12,X13,X11] :
        ( ~ r1_tarski(X11,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)),X13)
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(X13,X11)
        | ~ v1_relat_1(X11)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(k6_relat_1(X12))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X12)) )
    | ~ spl11_50 ),
    inference(resolution,[],[f7139,f4150])).

fof(f8761,plain,
    ( ~ spl11_9
    | spl11_68
    | ~ spl11_50 ),
    inference(avatar_split_clause,[],[f8754,f7138,f8759,f497])).

fof(f8754,plain,
    ( ! [X6,X4,X2,X5,X3] :
        ( ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X5)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X5)
        | ~ r1_tarski(X5,X3)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X6) )
    | ~ spl11_50 ),
    inference(resolution,[],[f7139,f1544])).

fof(f8647,plain,
    ( ~ spl11_9
    | spl11_66
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f8638,f7129,f8645,f497])).

fof(f8638,plain,
    ( ! [X8,X9] :
        ( ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)),X8)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(k6_relat_1(X9))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X9)) )
    | ~ spl11_48 ),
    inference(resolution,[],[f7130,f4150])).

fof(f8643,plain,
    ( ~ spl11_9
    | spl11_64
    | ~ spl11_48 ),
    inference(avatar_split_clause,[],[f8636,f7129,f8641,f497])).

fof(f8636,plain,
    ( ! [X4,X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3)
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X4) )
    | ~ spl11_48 ),
    inference(resolution,[],[f7130,f1544])).

fof(f8627,plain,
    ( ~ spl11_9
    | ~ spl11_5
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f7136,f491,f74,f497])).

fof(f7136,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl11_6 ),
    inference(duplicate_literal_removal,[],[f7132])).

fof(f7132,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl11_6 ),
    inference(resolution,[],[f492,f87])).

fof(f8614,plain,
    ( ~ spl11_15
    | ~ spl11_1
    | ~ spl11_11
    | spl11_3 ),
    inference(avatar_split_clause,[],[f8562,f68,f512,f58,f532])).

fof(f68,plain,
    ( spl11_3
  <=> ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f8562,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl11_3 ),
    inference(resolution,[],[f8515,f69])).

fof(f69,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f8613,plain,
    ( spl11_62
    | ~ spl11_15
    | ~ spl11_1
    | ~ spl11_11
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f8586,f598,f512,f58,f532,f8611])).

fof(f598,plain,
    ( spl11_22
  <=> ! [X3,X5,X7,X4,X6] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X7)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X7,X4)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_22])])).

fof(f8586,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X6,sK1)
        | ~ r1_tarski(sK1,X7)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X7,X9) )
    | ~ spl11_22 ),
    inference(duplicate_literal_removal,[],[f8558])).

fof(f8558,plain,
    ( ! [X6,X8,X7,X9] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X6,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X7)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X6)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X9,X8)
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X7,X9) )
    | ~ spl11_22 ),
    inference(resolution,[],[f8515,f599])).

fof(f599,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X7)
        | ~ r1_tarski(X3,sK1)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X7,X4)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X6,X3)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X4,X5) )
    | ~ spl11_22 ),
    inference(avatar_component_clause,[],[f598])).

fof(f8609,plain,
    ( ~ spl11_61
    | ~ spl11_15
    | ~ spl11_1
    | ~ spl11_11
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f8587,f526,f512,f58,f532,f8607])).

fof(f526,plain,
    ( spl11_12
  <=> ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f8587,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl11_12 ),
    inference(duplicate_literal_removal,[],[f8557])).

fof(f8557,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ v1_relat_1(sK1)
    | ~ spl11_12 ),
    inference(resolution,[],[f8515,f527])).

fof(f527,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X0)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X0) )
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f526])).

fof(f8602,plain,
    ( spl11_58
    | ~ spl11_15
    | ~ spl11_1
    | ~ spl11_11
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f8588,f560,f512,f58,f532,f8600])).

fof(f560,plain,
    ( spl11_16
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f8588,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X5,sK1)
        | ~ r1_tarski(sK1,X5)
        | ~ v1_relat_1(X5) )
    | ~ spl11_16 ),
    inference(duplicate_literal_removal,[],[f8556])).

fof(f8556,plain,
    ( ! [X5] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X5,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X5)
        | ~ v1_relat_1(X5) )
    | ~ spl11_16 ),
    inference(resolution,[],[f8515,f561])).

fof(f561,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f560])).

fof(f8598,plain,
    ( spl11_56
    | ~ spl11_15
    | ~ spl11_1
    | ~ spl11_11
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f8589,f574,f512,f58,f532,f8596])).

fof(f574,plain,
    ( spl11_18
  <=> ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f8589,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(sK1,X4)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3) )
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f8555])).

fof(f8555,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X3,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X4)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3) )
    | ~ spl11_18 ),
    inference(resolution,[],[f8515,f575])).

fof(f575,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X3)
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f574])).

fof(f8594,plain,
    ( spl11_54
    | ~ spl11_15
    | ~ spl11_1
    | ~ spl11_11
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f8590,f586,f512,f58,f532,f8592])).

fof(f586,plain,
    ( spl11_20
  <=> ! [X3,X5,X2,X4] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X5)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X4,X2)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f8590,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl11_20 ),
    inference(duplicate_literal_removal,[],[f8554])).

fof(f8554,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k6_relat_1(sK0))
        | ~ v1_relat_1(sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(sK1)
        | ~ r1_tarski(sK1,X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl11_20 ),
    inference(resolution,[],[f8515,f587])).

fof(f587,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X5)
        | ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X3)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X4,X2)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X3,X4) )
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f586])).

fof(f7144,plain,
    ( ~ spl11_9
    | spl11_52
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f7135,f491,f7142,f497])).

fof(f7135,plain,
    ( ! [X5] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),k6_relat_1(X5)) )
    | ~ spl11_6 ),
    inference(resolution,[],[f492,f4150])).

fof(f7140,plain,
    ( ~ spl11_9
    | spl11_50
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f7133,f491,f7138,f497])).

fof(f7133,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X2) )
    | ~ spl11_6 ),
    inference(resolution,[],[f492,f1544])).

fof(f7131,plain,
    ( spl11_48
    | ~ spl11_9
    | spl11_5 ),
    inference(avatar_split_clause,[],[f7126,f74,f497,f7129])).

fof(f7126,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X1) )
    | ~ spl11_5 ),
    inference(resolution,[],[f75,f1544])).

fof(f7123,plain,
    ( ~ spl11_15
    | ~ spl11_3
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f558,f526,f68,f532])).

fof(f558,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl11_12 ),
    inference(duplicate_literal_removal,[],[f556])).

fof(f556,plain,
    ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1)
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl11_12 ),
    inference(resolution,[],[f527,f87])).

fof(f7122,plain,
    ( ~ spl11_15
    | spl11_12
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f572,f560,f526,f532])).

fof(f572,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl11_16 ),
    inference(duplicate_literal_removal,[],[f570])).

fof(f570,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_16 ),
    inference(resolution,[],[f561,f87])).

fof(f7121,plain,
    ( ~ spl11_15
    | spl11_16
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f584,f574,f560,f532])).

fof(f584,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0) )
    | ~ spl11_18 ),
    inference(duplicate_literal_removal,[],[f582])).

fof(f582,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_18 ),
    inference(resolution,[],[f575,f87])).

fof(f7120,plain,
    ( ~ spl11_15
    | spl11_18
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f596,f586,f574,f532])).

fof(f596,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X1,X2) )
    | ~ spl11_20 ),
    inference(duplicate_literal_removal,[],[f594])).

fof(f594,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_20 ),
    inference(resolution,[],[f587,f87])).

fof(f7119,plain,
    ( ~ spl11_15
    | spl11_20
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f1245,f598,f586,f532])).

fof(f1245,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X1,X3) )
    | ~ spl11_22 ),
    inference(duplicate_literal_removal,[],[f1243])).

fof(f1243,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X0)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X1,X3)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1)) )
    | ~ spl11_22 ),
    inference(resolution,[],[f599,f87])).

fof(f7118,plain,
    ( ~ spl11_15
    | spl11_46
    | ~ spl11_32 ),
    inference(avatar_split_clause,[],[f7113,f4301,f7116,f532])).

fof(f7116,plain,
    ( spl11_46
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X4)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,k6_relat_1(X2))
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)),X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f4301,plain,
    ( spl11_32
  <=> ! [X9,X11,X10] :
        ( ~ v1_relat_1(k6_relat_1(X9))
        | ~ r1_tarski(X11,X10)
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)),X11)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)))
        | ~ r1_tarski(X10,sK1)
        | ~ v1_relat_1(X10)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_32])])).

fof(f7113,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)),X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),k6_relat_1(X2)))
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k6_relat_1(X2))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3)
        | ~ r1_tarski(X3,k6_relat_1(X2))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X4) )
    | ~ spl11_32 ),
    inference(resolution,[],[f4302,f1544])).

fof(f4302,plain,
    ( ! [X10,X11,X9] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X9))
        | ~ r1_tarski(X11,X10)
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)),X11)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)))
        | ~ r1_tarski(X10,sK1)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(k6_relat_1(X9)) )
    | ~ spl11_32 ),
    inference(avatar_component_clause,[],[f4301])).

fof(f4463,plain,
    ( ~ spl11_15
    | spl11_44
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f4455,f4305,f4461,f532])).

fof(f4305,plain,
    ( spl11_34
  <=> ! [X13,X12] :
        ( ~ v1_relat_1(k6_relat_1(X12))
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)),X13)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)))
        | ~ r1_tarski(X13,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_34])])).

fof(f4455,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_relat_1(X4)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X4)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X6,k6_relat_1(X5))
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X6) )
    | ~ spl11_34 ),
    inference(resolution,[],[f4306,f486])).

fof(f4306,plain,
    ( ! [X12,X13] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X12))
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)),X13)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)))
        | ~ r1_tarski(X13,sK1)
        | ~ v1_relat_1(k6_relat_1(X12)) )
    | ~ spl11_34 ),
    inference(avatar_component_clause,[],[f4305])).

fof(f4459,plain,
    ( ~ spl11_15
    | spl11_42
    | ~ spl11_34 ),
    inference(avatar_split_clause,[],[f4454,f4305,f4457,f532])).

fof(f4457,plain,
    ( spl11_42
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X3)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,k6_relat_1(X1))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_42])])).

fof(f4454,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)),X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X1)))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X2)
        | ~ r1_tarski(X2,k6_relat_1(X1))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X3) )
    | ~ spl11_34 ),
    inference(resolution,[],[f4306,f1544])).

fof(f4342,plain,
    ( ~ spl11_15
    | spl11_40
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f4334,f4309,f4340,f532])).

fof(f4309,plain,
    ( spl11_36
  <=> ! [X14] :
        ( ~ v1_relat_1(k6_relat_1(X14))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X14),k6_relat_1(X14)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X14),k6_relat_1(X14)),sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X14)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_36])])).

fof(f4334,plain,
    ( ! [X4,X3] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X3),k6_relat_1(X3)),sK1)
        | ~ v1_relat_1(k6_relat_1(X3))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X4,k6_relat_1(X3))
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X4) )
    | ~ spl11_36 ),
    inference(resolution,[],[f4310,f486])).

fof(f4310,plain,
    ( ! [X14] :
        ( ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X14))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X14),k6_relat_1(X14)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X14),k6_relat_1(X14)),sK1)
        | ~ v1_relat_1(k6_relat_1(X14)) )
    | ~ spl11_36 ),
    inference(avatar_component_clause,[],[f4309])).

fof(f4338,plain,
    ( ~ spl11_15
    | spl11_38
    | ~ spl11_36 ),
    inference(avatar_split_clause,[],[f4333,f4309,f4336,f532])).

fof(f4336,plain,
    ( spl11_38
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X2)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f4333,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)),sK1)
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X1,k6_relat_1(X0))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X2) )
    | ~ spl11_36 ),
    inference(resolution,[],[f4310,f1544])).

fof(f4311,plain,
    ( spl11_36
    | ~ spl11_15
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f4283,f526,f532,f4309])).

fof(f4283,plain,
    ( ! [X14] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X14))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X14))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X14),k6_relat_1(X14)),sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X14),k6_relat_1(X14))) )
    | ~ spl11_12 ),
    inference(resolution,[],[f4150,f527])).

fof(f4307,plain,
    ( spl11_34
    | ~ spl11_15
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f4282,f560,f532,f4305])).

fof(f4282,plain,
    ( ! [X12,X13] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X12))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X12))
        | ~ r1_tarski(X13,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X12),k6_relat_1(X12)),X13)
        | ~ v1_relat_1(X13) )
    | ~ spl11_16 ),
    inference(resolution,[],[f4150,f561])).

fof(f4303,plain,
    ( spl11_32
    | ~ spl11_15
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f4281,f574,f532,f4301])).

fof(f4281,plain,
    ( ! [X10,X11,X9] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X9))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X9))
        | ~ r1_tarski(X10,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X9),k6_relat_1(X9)),X11)
        | ~ v1_relat_1(X10)
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(X11,X10) )
    | ~ spl11_18 ),
    inference(resolution,[],[f4150,f575])).

fof(f4299,plain,
    ( spl11_30
    | ~ spl11_15
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f4280,f586,f532,f4297])).

fof(f4297,plain,
    ( spl11_30
  <=> ! [X5,X7,X8,X6] :
        ( ~ v1_relat_1(k6_relat_1(X5))
        | ~ r1_tarski(X7,X8)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X7)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ r1_tarski(X6,sK1)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X6)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_30])])).

fof(f4280,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X5))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X5))
        | ~ r1_tarski(X6,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X5),k6_relat_1(X5)),X7)
        | ~ v1_relat_1(X6)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X8,X6)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X7,X8) )
    | ~ spl11_20 ),
    inference(resolution,[],[f4150,f587])).

fof(f4295,plain,
    ( spl11_28
    | ~ spl11_15
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f4279,f598,f532,f4293])).

fof(f4293,plain,
    ( spl11_28
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(X2,X4)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)),X2)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X3)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_28])])).

fof(f4279,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(k6_relat_1(X0))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),k6_relat_1(X0))
        | ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)))
        | ~ r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X0)),X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X4,X3)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X2,X4) )
    | ~ spl11_22 ),
    inference(resolution,[],[f4150,f599])).

fof(f2365,plain,
    ( spl11_26
    | ~ spl11_15
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f2351,f598,f532,f2363])).

fof(f2363,plain,
    ( spl11_26
  <=> ! [X9,X11,X13,X15,X10,X12,X14] :
        ( ~ v1_relat_1(X9)
        | ~ r1_tarski(X13,X15)
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(X11,X13)
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(X12,sK1)
        | ~ v1_relat_1(X15)
        | ~ r1_tarski(X15,X14)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X14)
        | ~ r1_tarski(X14,X12)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X10)
        | ~ r1_tarski(X9,X11)
        | ~ v1_relat_1(X10)
        | ~ r1_tarski(X10,X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_26])])).

fof(f2351,plain,
    ( ! [X14,X12,X10,X15,X13,X11,X9] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ v1_relat_1(X9)
        | ~ v1_relat_1(X10)
        | ~ r1_tarski(X10,X9)
        | ~ r1_tarski(X9,X11)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X10)
        | ~ r1_tarski(X12,sK1)
        | ~ v1_relat_1(X11)
        | ~ r1_tarski(X11,X13)
        | ~ v1_relat_1(X14)
        | ~ r1_tarski(X14,X12)
        | ~ v1_relat_1(X12)
        | ~ v1_relat_1(X13)
        | ~ r1_tarski(X15,X14)
        | ~ v1_relat_1(X15)
        | ~ r1_tarski(X13,X15) )
    | ~ spl11_22 ),
    inference(resolution,[],[f1544,f599])).

fof(f1249,plain,
    ( ~ spl11_15
    | spl11_24
    | ~ spl11_22 ),
    inference(avatar_split_clause,[],[f1244,f598,f1247,f532])).

fof(f1247,plain,
    ( spl11_24
  <=> ! [X9,X5,X7,X8,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X9)
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(X9,X5)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X8,X7)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X7,X4)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X6,X8)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X5,X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_24])])).

fof(f1244,plain,
    ( ! [X6,X4,X8,X7,X5,X9] :
        ( ~ r1_tarski(X4,sK1)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(X7,X4)
        | ~ v1_relat_1(X4)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X8,X7)
        | ~ v1_relat_1(X8)
        | ~ r1_tarski(X6,X8)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X9,X5)
        | ~ v1_relat_1(X9)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X9) )
    | ~ spl11_22 ),
    inference(resolution,[],[f599,f486])).

fof(f600,plain,
    ( ~ spl11_15
    | spl11_22
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f595,f586,f598,f532])).

fof(f595,plain,
    ( ! [X6,X4,X7,X5,X3] :
        ( ~ r1_tarski(X3,sK1)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X5)
        | ~ v1_relat_1(X3)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(X6,X3)
        | ~ v1_relat_1(X6)
        | ~ r1_tarski(X5,X6)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X7,X4)
        | ~ v1_relat_1(X7)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X7) )
    | ~ spl11_20 ),
    inference(resolution,[],[f587,f486])).

fof(f588,plain,
    ( ~ spl11_15
    | spl11_20
    | ~ spl11_18 ),
    inference(avatar_split_clause,[],[f583,f574,f586,f532])).

fof(f583,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ r1_tarski(X2,sK1)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(X3,X4)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X4)
        | ~ r1_tarski(X4,X2)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X5,X3)
        | ~ v1_relat_1(X5)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X5) )
    | ~ spl11_18 ),
    inference(resolution,[],[f575,f486])).

fof(f576,plain,
    ( ~ spl11_15
    | spl11_18
    | ~ spl11_16 ),
    inference(avatar_split_clause,[],[f571,f560,f574,f532])).

fof(f571,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(X1,sK1)
        | ~ v1_relat_1(X2)
        | ~ r1_tarski(X2,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X3,X2)
        | ~ v1_relat_1(X3)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X3) )
    | ~ spl11_16 ),
    inference(resolution,[],[f561,f486])).

fof(f562,plain,
    ( ~ spl11_15
    | spl11_16
    | ~ spl11_12 ),
    inference(avatar_split_clause,[],[f557,f526,f560,f532])).

fof(f557,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X1,X0)
        | ~ v1_relat_1(X1)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X1) )
    | ~ spl11_12 ),
    inference(resolution,[],[f527,f486])).

fof(f536,plain,
    ( ~ spl11_11
    | ~ spl11_1
    | spl11_15 ),
    inference(avatar_split_clause,[],[f535,f532,f58,f512])).

fof(f535,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl11_15 ),
    inference(resolution,[],[f533,f36])).

fof(f533,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f532])).

fof(f534,plain,
    ( spl11_12
    | ~ spl11_15
    | spl11_3 ),
    inference(avatar_split_clause,[],[f524,f68,f532,f526])).

fof(f524,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(k6_relat_1(sK0),sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),X0) )
    | ~ spl11_3 ),
    inference(resolution,[],[f69,f486])).

fof(f523,plain,(
    spl11_11 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | ~ spl11_11 ),
    inference(resolution,[],[f513,f51])).

fof(f513,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ spl11_11 ),
    inference(avatar_component_clause,[],[f512])).

fof(f514,plain,
    ( ~ spl11_1
    | ~ spl11_11
    | spl11_9 ),
    inference(avatar_split_clause,[],[f507,f497,f512,f58])).

fof(f507,plain,
    ( ~ v1_relat_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl11_9 ),
    inference(resolution,[],[f498,f36])).

fof(f498,plain,
    ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f497])).

fof(f499,plain,
    ( spl11_6
    | ~ spl11_9
    | spl11_5 ),
    inference(avatar_split_clause,[],[f487,f74,f497,f491])).

fof(f487,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k5_relat_1(sK1,k6_relat_1(sK0)))
        | ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),X0) )
    | ~ spl11_5 ),
    inference(resolution,[],[f486,f75])).

fof(f76,plain,
    ( ~ spl11_3
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f29,f74,f68])).

fof(f29,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k6_relat_1(sK0)),sK1)
    | ~ r1_tarski(k5_relat_1(k6_relat_1(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        | ~ r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
          & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/relat_1__t76_relat_1.p',t76_relat_1)).

fof(f63,plain,(
    spl11_0 ),
    inference(avatar_split_clause,[],[f30,f61])).

fof(f61,plain,
    ( spl11_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f30,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
