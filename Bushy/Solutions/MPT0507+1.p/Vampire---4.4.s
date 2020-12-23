%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t105_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:47 EDT 2019

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 134 expanded)
%              Number of leaves         :    8 (  36 expanded)
%              Depth                    :   22
%              Number of atoms          :  194 ( 431 expanded)
%              Number of equality atoms :    4 (  15 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3255,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f69,f79,f87,f3253])).

fof(f3253,plain,
    ( ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f3252])).

fof(f3252,plain,
    ( $false
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_7 ),
    inference(subsumption_resolution,[],[f86,f3251])).

fof(f3251,plain,
    ( ! [X2] : r1_tarski(k7_relat_1(sK1,X2),k7_relat_1(sK2,X2))
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3250,f75])).

fof(f75,plain,
    ( ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))
    | ~ spl9_2 ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t105_relat_1.p',dt_k7_relat_1)).

fof(f68,plain,
    ( v1_relat_1(sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl9_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f3250,plain,
    ( ! [X2] :
        ( r1_tarski(k7_relat_1(sK1,X2),k7_relat_1(sK2,X2))
        | ~ v1_relat_1(k7_relat_1(sK1,X2)) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f3240])).

fof(f3240,plain,
    ( ! [X2] :
        ( r1_tarski(k7_relat_1(sK1,X2),k7_relat_1(sK2,X2))
        | ~ v1_relat_1(k7_relat_1(sK1,X2))
        | r1_tarski(k7_relat_1(sK1,X2),k7_relat_1(sK2,X2)) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f3197,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/relat_1__t105_relat_1.p',d3_relat_1)).

fof(f3197,plain,
    ( ! [X4,X5] :
        ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X4),X5),sK7(k7_relat_1(sK1,X4),X5)),k7_relat_1(sK2,X4))
        | r1_tarski(k7_relat_1(sK1,X4),X5) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3196,f64])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl9_0
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f3196,plain,
    ( ! [X4,X5] :
        ( r1_tarski(k7_relat_1(sK1,X4),X5)
        | ~ v1_relat_1(sK2)
        | r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X4),X5),sK7(k7_relat_1(sK1,X4),X5)),k7_relat_1(sK2,X4)) )
    | ~ spl9_0
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f3195,f72])).

fof(f72,plain,
    ( ! [X3] : v1_relat_1(k7_relat_1(sK2,X3))
    | ~ spl9_0 ),
    inference(resolution,[],[f64,f39])).

fof(f3195,plain,
    ( ! [X4,X5] :
        ( r1_tarski(k7_relat_1(sK1,X4),X5)
        | ~ v1_relat_1(k7_relat_1(sK2,X4))
        | ~ v1_relat_1(sK2)
        | r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X4),X5),sK7(k7_relat_1(sK1,X4),X5)),k7_relat_1(sK2,X4)) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f3172,f61])).

fof(f61,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP5(X4,X3,X1,X0)
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ sP5(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t105_relat_1.p',d11_relat_1)).

fof(f3172,plain,
    ( ! [X4,X5] :
        ( sP5(sK7(k7_relat_1(sK1,X4),X5),sK6(k7_relat_1(sK1,X4),X5),X4,sK2)
        | r1_tarski(k7_relat_1(sK1,X4),X5) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(duplicate_literal_removal,[],[f3171])).

fof(f3171,plain,
    ( ! [X4,X5] :
        ( r1_tarski(k7_relat_1(sK1,X4),X5)
        | sP5(sK7(k7_relat_1(sK1,X4),X5),sK6(k7_relat_1(sK1,X4),X5),X4,sK2)
        | r1_tarski(k7_relat_1(sK1,X4),X5) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f514,f2208])).

fof(f2208,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X2),X3),sK7(k7_relat_1(sK1,X2),X3)),sK2)
        | r1_tarski(k7_relat_1(sK1,X2),X3) )
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(resolution,[],[f1180,f78])).

fof(f78,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl9_4
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f1180,plain,
    ( ! [X2,X3,X1] :
        ( ~ r1_tarski(sK1,X3)
        | r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X1),X2),sK7(k7_relat_1(sK1,X1),X2)),X3)
        | r1_tarski(k7_relat_1(sK1,X1),X2) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f1171,f68])).

fof(f1171,plain,
    ( ! [X2,X3,X1] :
        ( r1_tarski(k7_relat_1(sK1,X1),X2)
        | ~ v1_relat_1(sK1)
        | r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X1),X2),sK7(k7_relat_1(sK1,X1),X2)),X3)
        | ~ r1_tarski(sK1,X3) )
    | ~ spl9_2 ),
    inference(resolution,[],[f497,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f497,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X2),X3),sK7(k7_relat_1(sK1,X2),X3)),sK1)
        | r1_tarski(k7_relat_1(sK1,X2),X3) )
    | ~ spl9_2 ),
    inference(resolution,[],[f303,f42])).

fof(f42,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP5(X4,X3,X1,X0)
      | r2_hidden(k4_tarski(X3,X4),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f303,plain,
    ( ! [X0,X1] :
        ( sP5(sK7(k7_relat_1(sK1,X0),X1),sK6(k7_relat_1(sK1,X0),X1),X0,sK1)
        | r1_tarski(k7_relat_1(sK1,X0),X1) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f302,f68])).

fof(f302,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(sK1,X0),X1)
        | sP5(sK7(k7_relat_1(sK1,X0),X1),sK6(k7_relat_1(sK1,X0),X1),X0,sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f292,f75])).

fof(f292,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(sK1,X0),X1)
        | ~ v1_relat_1(k7_relat_1(sK1,X0))
        | sP5(sK7(k7_relat_1(sK1,X0),X1),sK6(k7_relat_1(sK1,X0),X1),X0,sK1)
        | ~ v1_relat_1(sK1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | sP5(X4,X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | sP5(X4,X3,X1,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f88,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X0),X1),sK7(k7_relat_1(sK1,X0),X1)),k7_relat_1(sK1,X0))
        | r1_tarski(k7_relat_1(sK1,X0),X1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f75,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK6(X0,X1),sK7(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f514,plain,
    ( ! [X14,X12,X15,X13] :
        ( ~ r2_hidden(k4_tarski(sK6(k7_relat_1(sK1,X12),X13),X14),X15)
        | r1_tarski(k7_relat_1(sK1,X12),X13)
        | sP5(X14,sK6(k7_relat_1(sK1,X12),X13),X12,X15) )
    | ~ spl9_2 ),
    inference(resolution,[],[f496,f40])).

fof(f40,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | sP5(X4,X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f496,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(k7_relat_1(sK1,X0),X1),X0)
        | r1_tarski(k7_relat_1(sK1,X0),X1) )
    | ~ spl9_2 ),
    inference(resolution,[],[f303,f41])).

fof(f41,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ sP5(X4,X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f86,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl9_7
  <=> ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f87,plain,(
    ~ spl9_7 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t105_relat_1.p',t105_relat_1)).

fof(f79,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f38,f67])).

fof(f38,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f65,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
