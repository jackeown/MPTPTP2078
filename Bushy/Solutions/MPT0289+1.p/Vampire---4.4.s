%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : zfmisc_1__t96_zfmisc_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:42:13 EDT 2019

% Result     : Theorem 11.94s
% Output     : Refutation 11.94s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 130 expanded)
%              Number of leaves         :   14 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :  196 ( 323 expanded)
%              Number of equality atoms :   18 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f442,f18477,f21784,f29575,f32476,f32478,f32481,f34108])).

fof(f34108,plain,
    ( spl7_17
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f34107])).

fof(f34107,plain,
    ( $false
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f34069,f33270])).

fof(f33270,plain,
    ( ! [X0] : r2_hidden(sK3(sK1,sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),k2_xboole_0(X0,sK1))
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f32612,f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t96_zfmisc_1.p',d3_xboole_0)).

fof(f32612,plain,
    ( r2_hidden(sK3(sK1,sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl7_18 ),
    inference(resolution,[],[f435,f54])).

fof(f54,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t96_zfmisc_1.p',d4_tarski)).

fof(f435,plain,
    ( r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl7_18
  <=> r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f34069,plain,
    ( ~ r2_hidden(sK3(sK1,sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl7_17
    | ~ spl7_18 ),
    inference(unit_resulting_resolution,[],[f32611,f33062])).

fof(f33062,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK0,sK1))
        | ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),X0) )
    | ~ spl7_17 ),
    inference(resolution,[],[f426,f53])).

fof(f53,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f426,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl7_17
  <=> ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f32611,plain,
    ( r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),sK3(sK1,sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))))
    | ~ spl7_18 ),
    inference(resolution,[],[f435,f55])).

fof(f55,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK3(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK3(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f32481,plain,
    ( ~ spl7_16
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f32480])).

fof(f32480,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f441,f32479])).

fof(f32479,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f21875,f28])).

fof(f28,plain,(
    k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) != k3_tarski(k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) != k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) = k3_tarski(k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t96_zfmisc_1.p',t96_zfmisc_1)).

fof(f21875,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) = k3_tarski(k2_xboole_0(sK0,sK1))
    | ~ spl7_16 ),
    inference(resolution,[],[f429,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X0)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f429,plain,
    ( r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl7_16
  <=> r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f441,plain,
    ( r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl7_20
  <=> r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f32478,plain,
    ( ~ spl7_16
    | spl7_21
    | ~ spl7_582 ),
    inference(avatar_contradiction_clause,[],[f32477])).

fof(f32477,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_21
    | ~ spl7_582 ),
    inference(subsumption_resolution,[],[f29574,f32438])).

fof(f32438,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK0)
    | ~ spl7_16
    | ~ spl7_21 ),
    inference(unit_resulting_resolution,[],[f21861,f21822])).

fof(f21822,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),X0) )
    | ~ spl7_21 ),
    inference(resolution,[],[f438,f53])).

fof(f438,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl7_21
  <=> ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f21861,plain,
    ( r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))))
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f429,f55])).

fof(f29574,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK0)
    | ~ spl7_582 ),
    inference(avatar_component_clause,[],[f29573])).

fof(f29573,plain,
    ( spl7_582
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_582])])).

fof(f32476,plain,
    ( ~ spl7_16
    | spl7_19
    | ~ spl7_580 ),
    inference(avatar_contradiction_clause,[],[f32475])).

fof(f32475,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_19
    | ~ spl7_580 ),
    inference(subsumption_resolution,[],[f32439,f29568])).

fof(f29568,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl7_580 ),
    inference(avatar_component_clause,[],[f29567])).

fof(f29567,plain,
    ( spl7_580
  <=> r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_580])])).

fof(f32439,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl7_16
    | ~ spl7_19 ),
    inference(unit_resulting_resolution,[],[f21861,f21560])).

fof(f21560,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),X0) )
    | ~ spl7_19 ),
    inference(resolution,[],[f432,f53])).

fof(f432,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f431])).

fof(f431,plain,
    ( spl7_19
  <=> ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f29575,plain,
    ( spl7_580
    | spl7_582
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f29542,f428,f29573,f29567])).

fof(f29542,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK0)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),sK1)
    | ~ spl7_16 ),
    inference(resolution,[],[f21862,f58])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f21862,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1)))),k2_xboole_0(sK0,sK1))
    | ~ spl7_16 ),
    inference(unit_resulting_resolution,[],[f429,f54])).

fof(f21784,plain,
    ( spl7_17
    | ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f21783])).

fof(f21783,plain,
    ( $false
    | ~ spl7_17
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f21768,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t96_zfmisc_1.p',t7_xboole_1)).

fof(f21768,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | ~ spl7_17
    | ~ spl7_20 ),
    inference(resolution,[],[f21689,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t96_zfmisc_1.p',t95_zfmisc_1)).

fof(f21689,plain,
    ( ~ r1_tarski(k3_tarski(sK0),k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl7_17
    | ~ spl7_20 ),
    inference(unit_resulting_resolution,[],[f441,f426,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/zfmisc_1__t96_zfmisc_1.p',d3_tarski)).

fof(f18477,plain,
    ( ~ spl7_16
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f18476])).

fof(f18476,plain,
    ( $false
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f18475,f28])).

fof(f18475,plain,
    ( k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) = k3_tarski(k2_xboole_0(sK0,sK1))
    | ~ spl7_16
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f18429,f429])).

fof(f18429,plain,
    ( ~ r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(k2_xboole_0(sK0,sK1)))
    | k2_xboole_0(k3_tarski(sK0),k3_tarski(sK1)) = k3_tarski(k2_xboole_0(sK0,sK1))
    | ~ spl7_18 ),
    inference(resolution,[],[f435,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1,X2),X1)
      | ~ r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f442,plain,
    ( spl7_16
    | spl7_18
    | spl7_20 ),
    inference(avatar_split_clause,[],[f382,f440,f434,f428])).

fof(f382,plain,
    ( r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK0))
    | r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(sK1))
    | r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),k3_tarski(k2_xboole_0(sK0,sK1))),k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2] :
      ( k3_tarski(k2_xboole_0(sK0,sK1)) != X2
      | r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),X2),k3_tarski(sK0))
      | r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),X2),k3_tarski(sK1))
      | r2_hidden(sK5(k3_tarski(sK0),k3_tarski(sK1),X2),X2) ) ),
    inference(superposition,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(X0,X1,X2),X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r2_hidden(sK5(X0,X1,X2),X2)
      | k2_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
