%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t21_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:00 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   13
%              Number of atoms          :   98 ( 144 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1519,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f1518])).

fof(f1518,plain,
    ( ~ spl10_0
    | spl10_3 ),
    inference(avatar_contradiction_clause,[],[f1517])).

fof(f1517,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f1516,f72])).

fof(f72,plain,
    ( v1_relat_1(sK0)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl10_0
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f1516,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl10_0
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f1513,f77])).

fof(f77,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl10_3
  <=> ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1513,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | ~ spl10_0 ),
    inference(duplicate_literal_removal,[],[f1491])).

fof(f1491,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ v1_relat_1(sK0)
    | r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl10_0 ),
    inference(resolution,[],[f446,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t21_relat_1.p',d3_relat_1)).

fof(f446,plain,
    ( ! [X10,X11] :
        ( r2_hidden(k4_tarski(sK1(sK0,X10),sK2(sK0,X11)),k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
        | r1_tarski(sK0,X10)
        | r1_tarski(sK0,X11) )
    | ~ spl10_0 ),
    inference(resolution,[],[f148,f111])).

fof(f111,plain,
    ( ! [X1] :
        ( r2_hidden(sK2(sK0,X1),k2_relat_1(sK0))
        | r1_tarski(sK0,X1) )
    | ~ spl10_0 ),
    inference(resolution,[],[f81,f67])).

fof(f67,plain,(
    ! [X2,X0] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X2,X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t21_relat_1.p',d5_relat_1)).

fof(f81,plain,
    ( ! [X1] :
        ( sP4(sK2(sK0,X1),sK0)
        | r1_tarski(sK0,X1) )
    | ~ spl10_0 ),
    inference(resolution,[],[f74,f47])).

fof(f47,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | sP4(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f74,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK1(sK0,X0),sK2(sK0,X0)),sK0)
        | r1_tarski(sK0,X0) )
    | ~ spl10_0 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f148,plain,
    ( ! [X2,X3,X1] :
        ( ~ r2_hidden(X2,X3)
        | r1_tarski(sK0,X1)
        | r2_hidden(k4_tarski(sK1(sK0,X1),X2),k2_zfmisc_1(k1_relat_1(sK0),X3)) )
    | ~ spl10_0 ),
    inference(resolution,[],[f105,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t21_relat_1.p',t106_zfmisc_1)).

fof(f105,plain,
    ( ! [X1] :
        ( r2_hidden(sK1(sK0,X1),k1_relat_1(sK0))
        | r1_tarski(sK0,X1) )
    | ~ spl10_0 ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X2,X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t21_relat_1.p',d4_relat_1)).

fof(f80,plain,
    ( ! [X0] :
        ( sP7(sK1(sK0,X0),sK0)
        | r1_tarski(sK0,X0) )
    | ~ spl10_0 ),
    inference(resolution,[],[f74,f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | sP7(X2,X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,(
    ~ spl10_3 ),
    inference(avatar_split_clause,[],[f37,f76])).

fof(f37,plain,(
    ~ r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t21_relat_1.p',t21_relat_1)).

fof(f73,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
