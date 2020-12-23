%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t12_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:10 EDT 2019

% Result     : Theorem 8.87s
% Output     : Refutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 348 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   17
%              Number of atoms          :  334 (2213 expanded)
%              Number of equality atoms :   39 ( 214 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f58098,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f280,f284,f348,f56931,f57842,f58097])).

fof(f58097,plain,
    ( ~ spl12_0
    | ~ spl12_8
    | ~ spl12_156
    | spl12_159 ),
    inference(avatar_contradiction_clause,[],[f58048])).

fof(f58048,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_156
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f60,f57926,f57938,f55])).

fof(f55,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0))
      | r2_hidden(k4_tarski(sK1,sK3(X2)),sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                  & X1 != X3
                  & r2_hidden(k4_tarski(X1,X3),X0)
                  & r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r2_hidden(k4_tarski(X1,X2),X0)
              | ~ r2_hidden(X2,k3_relat_1(X0)) )
          & ? [X4] :
              ( ~ r2_hidden(k4_tarski(X4,X1),X0)
              & r2_hidden(X4,k3_relat_1(X0)) )
          & r2_hidden(X1,k3_relat_1(X0)) )
      & v2_wellord1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X4] :
                    ( ~ r2_hidden(k4_tarski(X4,X1),X0)
                    & r2_hidden(X4,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v2_wellord1(X0)
         => ! [X1] :
              ~ ( ! [X2] :
                    ~ ( ! [X3] :
                          ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                            & X1 != X3
                            & r2_hidden(k4_tarski(X1,X3),X0)
                            & r2_hidden(X3,k3_relat_1(X0)) )
                      & r2_hidden(k4_tarski(X1,X2),X0)
                      & r2_hidden(X2,k3_relat_1(X0)) )
                & ? [X2] :
                    ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
                & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ~ ( ~ r2_hidden(k4_tarski(X2,X3),X0)
                          & X1 != X3
                          & r2_hidden(k4_tarski(X1,X3),X0)
                          & r2_hidden(X3,k3_relat_1(X0)) )
                    & r2_hidden(k4_tarski(X1,X2),X0)
                    & r2_hidden(X2,k3_relat_1(X0)) )
              & ? [X2] :
                  ( ~ r2_hidden(k4_tarski(X2,X1),X0)
                  & r2_hidden(X2,k3_relat_1(X0)) )
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',t12_wellord1)).

fof(f57938,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK3(sK1)),sK0)
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_156
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f60,f57926,f57])).

fof(f57,plain,(
    ! [X2] :
      ( ~ r2_hidden(k4_tarski(sK1,X2),sK0)
      | ~ r2_hidden(X2,k3_relat_1(sK0))
      | ~ r2_hidden(k4_tarski(X2,sK3(X2)),sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f57926,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_156
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f61,f60,f57844,f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | r2_hidden(k4_tarski(X3,X1),X0)
      | r2_hidden(X3,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',s1_xboole_0__e7_18__wellord1)).

fof(f57844,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_156
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f51313,f51310,f6772])).

fof(f6772,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK4(sK0,X0),k3_relat_1(sK0))
        | ~ r2_hidden(X0,sK4(sK0,X0))
        | o_0_0_xboole_0 = sK4(sK0,X0) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(resolution,[],[f1036,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',t3_subset)).

fof(f1036,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK4(sK0,X1),k1_zfmisc_1(k3_relat_1(sK0)))
        | o_0_0_xboole_0 = sK4(sK0,X1)
        | ~ r2_hidden(X1,sK4(sK0,X1)) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(duplicate_literal_removal,[],[f1035])).

fof(f1035,plain,
    ( ! [X1] :
        ( o_0_0_xboole_0 = sK4(sK0,X1)
        | ~ m1_subset_1(sK4(sK0,X1),k1_zfmisc_1(k3_relat_1(sK0)))
        | ~ r2_hidden(X1,sK4(sK0,X1))
        | o_0_0_xboole_0 = sK4(sK0,X1)
        | ~ m1_subset_1(sK4(sK0,X1),k1_zfmisc_1(k3_relat_1(sK0))) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(resolution,[],[f550,f290])).

fof(f290,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(sK0,X1),X1)
        | o_0_0_xboole_0 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k3_relat_1(sK0))) )
    | ~ spl12_0 ),
    inference(resolution,[],[f273,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f273,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,k3_relat_1(sK0))
        | r2_hidden(sK5(sK0,X2),X2)
        | o_0_0_xboole_0 = X2 )
    | ~ spl12_0 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl12_0
  <=> ! [X2] :
        ( ~ r1_tarski(X2,k3_relat_1(sK0))
        | r2_hidden(sK5(sK0,X2),X2)
        | o_0_0_xboole_0 = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_0])])).

fof(f550,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(sK0,X3),sK4(sK0,X2))
        | o_0_0_xboole_0 = X3
        | ~ m1_subset_1(X3,k1_zfmisc_1(k3_relat_1(sK0)))
        | ~ r2_hidden(X2,X3) )
    | ~ spl12_8 ),
    inference(resolution,[],[f357,f110])).

fof(f110,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k4_tarski(X6,X7),sK0)
      | ~ r2_hidden(X6,sK4(sK0,X7)) ) ),
    inference(resolution,[],[f61,f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f357,plain,
    ( ! [X2,X3] :
        ( r2_hidden(k4_tarski(sK5(sK0,X2),X3),sK0)
        | ~ r2_hidden(X3,X2)
        | o_0_0_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k3_relat_1(sK0))) )
    | ~ spl12_8 ),
    inference(resolution,[],[f347,f84])).

fof(f347,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0)
        | ~ r2_hidden(X1,X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f346])).

fof(f346,plain,
    ( spl12_8
  <=> ! [X1,X0] :
        ( ~ r1_tarski(X0,k3_relat_1(sK0))
        | r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0)
        | ~ r2_hidden(X1,X0)
        | o_0_0_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f51310,plain,
    ( r1_tarski(sK4(sK0,sK1),k3_relat_1(sK0))
    | ~ spl12_156 ),
    inference(avatar_component_clause,[],[f51309])).

fof(f51309,plain,
    ( spl12_156
  <=> r1_tarski(sK4(sK0,sK1),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_156])])).

fof(f51313,plain,
    ( o_0_0_xboole_0 != sK4(sK0,sK1)
    | ~ spl12_159 ),
    inference(avatar_component_clause,[],[f51312])).

fof(f51312,plain,
    ( spl12_159
  <=> o_0_0_xboole_0 != sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_159])])).

fof(f61,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    r2_hidden(sK1,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f57842,plain,
    ( ~ spl12_0
    | ~ spl12_8
    | spl12_157
    | spl12_159 ),
    inference(avatar_contradiction_clause,[],[f57793])).

fof(f57793,plain,
    ( $false
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_157
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f60,f57569,f57581,f55])).

fof(f57581,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK3(sK1)),sK0)
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_157
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f60,f57569,f57])).

fof(f57569,plain,
    ( r2_hidden(k4_tarski(sK1,sK1),sK0)
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_157
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f61,f60,f57512,f66])).

fof(f57512,plain,
    ( ~ r2_hidden(sK1,sK4(sK0,sK1))
    | ~ spl12_0
    | ~ spl12_8
    | ~ spl12_157
    | ~ spl12_159 ),
    inference(unit_resulting_resolution,[],[f51313,f51307,f19003])).

fof(f19003,plain,
    ( ! [X4] :
        ( ~ r2_hidden(X4,sK4(sK0,X4))
        | o_0_0_xboole_0 = sK4(sK0,X4)
        | r1_tarski(sK4(sK0,X4),k3_relat_1(sK0)) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(resolution,[],[f7070,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',d3_tarski)).

fof(f7070,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK4(sK0,X0),k3_relat_1(sK0)),k3_relat_1(sK0))
        | ~ r2_hidden(X0,sK4(sK0,X0))
        | o_0_0_xboole_0 = sK4(sK0,X0) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(resolution,[],[f1105,f109])).

fof(f109,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,sK4(sK0,X5))
      | r2_hidden(X4,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f61,f64])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1105,plain,
    ( ! [X0] :
        ( r2_hidden(sK8(sK4(sK0,X0),k3_relat_1(sK0)),sK4(sK0,X0))
        | o_0_0_xboole_0 = sK4(sK0,X0)
        | ~ r2_hidden(X0,sK4(sK0,X0)) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(duplicate_literal_removal,[],[f1102])).

fof(f1102,plain,
    ( ! [X0] :
        ( o_0_0_xboole_0 = sK4(sK0,X0)
        | r2_hidden(sK8(sK4(sK0,X0),k3_relat_1(sK0)),sK4(sK0,X0))
        | ~ r2_hidden(X0,sK4(sK0,X0))
        | o_0_0_xboole_0 = sK4(sK0,X0)
        | r2_hidden(sK8(sK4(sK0,X0),k3_relat_1(sK0)),sK4(sK0,X0)) )
    | ~ spl12_0
    | ~ spl12_8 ),
    inference(resolution,[],[f573,f289])).

fof(f289,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(sK0,X0),X0)
        | o_0_0_xboole_0 = X0
        | r2_hidden(sK8(X0,k3_relat_1(sK0)),X0) )
    | ~ spl12_0 ),
    inference(resolution,[],[f273,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK8(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f573,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(sK5(sK0,X3),sK4(sK0,X2))
        | o_0_0_xboole_0 = X3
        | r2_hidden(sK8(X3,k3_relat_1(sK0)),X3)
        | ~ r2_hidden(X2,X3) )
    | ~ spl12_8 ),
    inference(resolution,[],[f356,f110])).

fof(f356,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0)
        | ~ r2_hidden(X1,X0)
        | o_0_0_xboole_0 = X0
        | r2_hidden(sK8(X0,k3_relat_1(sK0)),X0) )
    | ~ spl12_8 ),
    inference(resolution,[],[f347,f86])).

fof(f51307,plain,
    ( ~ r1_tarski(sK4(sK0,sK1),k3_relat_1(sK0))
    | ~ spl12_157 ),
    inference(avatar_component_clause,[],[f51306])).

fof(f51306,plain,
    ( spl12_157
  <=> ~ r1_tarski(sK4(sK0,sK1),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_157])])).

fof(f56931,plain,(
    ~ spl12_158 ),
    inference(avatar_contradiction_clause,[],[f56924])).

fof(f56924,plain,
    ( $false
    | ~ spl12_158 ),
    inference(unit_resulting_resolution,[],[f98,f55927])).

fof(f55927,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ spl12_158 ),
    inference(backward_demodulation,[],[f51316,f156])).

fof(f156,plain,(
    ~ v1_xboole_0(sK4(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f143,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',t7_boole)).

fof(f143,plain,(
    r2_hidden(sK2,sK4(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f61,f58,f59,f66])).

fof(f59,plain,(
    ~ r2_hidden(k4_tarski(sK2,sK1),sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    r2_hidden(sK2,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f51316,plain,
    ( o_0_0_xboole_0 = sK4(sK0,sK1)
    | ~ spl12_158 ),
    inference(avatar_component_clause,[],[f51315])).

fof(f51315,plain,
    ( spl12_158
  <=> o_0_0_xboole_0 = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_158])])).

fof(f98,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',dt_o_0_0_xboole_0)).

fof(f348,plain,
    ( spl12_8
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f118,f278,f346])).

fof(f278,plain,
    ( spl12_3
  <=> ~ v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK0)
      | ~ r1_tarski(X0,k3_relat_1(sK0))
      | o_0_0_xboole_0 = X0
      | ~ r2_hidden(X1,X0)
      | r2_hidden(k4_tarski(sK5(sK0,X0),X1),sK0) ) ),
    inference(resolution,[],[f62,f104])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | o_0_0_xboole_0 = X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) ) ),
    inference(definition_unfolding,[],[f67,f82])).

fof(f82,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',d2_xboole_0)).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k4_tarski(sK5(X0,X1),X3),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( r2_hidden(k4_tarski(X2,X3),X0)
                  | ~ r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
          | k1_xboole_0 = X1
          | ~ r1_tarski(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( ! [X2] :
                  ~ ( ! [X3] :
                        ( r2_hidden(X3,X1)
                       => r2_hidden(k4_tarski(X2,X3),X0) )
                    & r2_hidden(X2,X1) )
              & k1_xboole_0 != X1
              & r1_tarski(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t12_wellord1.p',t10_wellord1)).

fof(f62,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f284,plain,(
    spl12_3 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl12_3 ),
    inference(unit_resulting_resolution,[],[f61,f279])).

fof(f279,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f278])).

fof(f280,plain,
    ( spl12_0
    | ~ spl12_3 ),
    inference(avatar_split_clause,[],[f119,f278,f272])).

fof(f119,plain,(
    ! [X2] :
      ( ~ v1_relat_1(sK0)
      | ~ r1_tarski(X2,k3_relat_1(sK0))
      | o_0_0_xboole_0 = X2
      | r2_hidden(sK5(sK0,X2),X2) ) ),
    inference(resolution,[],[f62,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | o_0_0_xboole_0 = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v2_wellord1(X0)
      | ~ r1_tarski(X1,k3_relat_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
