%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:32 EST 2020

% Result     : Theorem 2.50s
% Output     : Refutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 135 expanded)
%              Number of leaves         :   12 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :  225 ( 364 expanded)
%              Number of equality atoms :   27 (  65 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f407,f483,f484,f1221,f2118,f2167])).

fof(f2167,plain,
    ( ~ spl32_3
    | spl32_4 ),
    inference(avatar_contradiction_clause,[],[f2166])).

fof(f2166,plain,
    ( $false
    | ~ spl32_3
    | spl32_4 ),
    inference(subsumption_resolution,[],[f2150,f2135])).

fof(f2135,plain,
    ( ! [X2,X1] : ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),X1),k2_zfmisc_1(sK0,X2))
    | spl32_4 ),
    inference(resolution,[],[f482,f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f482,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | spl32_4 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl32_4
  <=> r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_4])])).

fof(f2150,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl32_3 ),
    inference(resolution,[],[f477,f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f477,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ spl32_3 ),
    inference(avatar_component_clause,[],[f476])).

fof(f476,plain,
    ( spl32_3
  <=> r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_3])])).

fof(f2118,plain,
    ( ~ spl32_1
    | spl32_3
    | ~ spl32_4 ),
    inference(avatar_contradiction_clause,[],[f2117])).

fof(f2117,plain,
    ( $false
    | ~ spl32_1
    | spl32_3
    | ~ spl32_4 ),
    inference(subsumption_resolution,[],[f2116,f1261])).

fof(f1261,plain,
    ( r2_hidden(sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_relat_1(sK1))
    | ~ spl32_1 ),
    inference(resolution,[],[f402,f100])).

fof(f100,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f402,plain,
    ( r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)
    | ~ spl32_1 ),
    inference(avatar_component_clause,[],[f400])).

fof(f400,plain,
    ( spl32_1
  <=> r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).

fof(f2116,plain,
    ( ~ r2_hidden(sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_relat_1(sK1))
    | ~ spl32_1
    | spl32_3
    | ~ spl32_4 ),
    inference(subsumption_resolution,[],[f2099,f481])).

fof(f481,plain,
    ( r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | ~ spl32_4 ),
    inference(avatar_component_clause,[],[f480])).

fof(f2099,plain,
    ( ~ r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | ~ r2_hidden(sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_relat_1(sK1))
    | ~ spl32_1
    | spl32_3 ),
    inference(resolution,[],[f1293,f105])).

fof(f105,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1293,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | ~ spl32_1
    | spl32_3 ),
    inference(subsumption_resolution,[],[f1283,f402])).

fof(f1283,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)
    | ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | spl32_3 ),
    inference(resolution,[],[f478,f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f478,plain,
    ( ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | spl32_3 ),
    inference(avatar_component_clause,[],[f476])).

fof(f1221,plain,(
    spl32_2 ),
    inference(avatar_contradiction_clause,[],[f1220])).

fof(f1220,plain,
    ( $false
    | spl32_2 ),
    inference(subsumption_resolution,[],[f1204,f779])).

fof(f779,plain,
    ( ! [X2,X1] : ~ r2_hidden(sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_zfmisc_1(X1,X2))
    | spl32_2 ),
    inference(resolution,[],[f409,f164])).

fof(f164,plain,(
    ! [X0,X3,X1] :
      ( sQ31_eqProxy(k4_tarski(sK17(X0,X1,X3),sK18(X0,X1,X3)),X3)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_proxy_replacement,[],[f106,f129])).

fof(f129,plain,(
    ! [X1,X0] :
      ( sQ31_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ31_eqProxy])])).

fof(f106,plain,(
    ! [X0,X3,X1] :
      ( k4_tarski(sK17(X0,X1,X3),sK18(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_tarski(sK17(X0,X1,X3),sK18(X0,X1,X3)) = X3
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f409,plain,
    ( ! [X0,X1] : ~ sQ31_eqProxy(k4_tarski(X0,X1),sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))))
    | spl32_2 ),
    inference(resolution,[],[f406,f155])).

fof(f155,plain,(
    ! [X2,X0,X3] :
      ( ~ sQ31_eqProxy(k4_tarski(X2,X3),sK4(X0))
      | v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f50,f129])).

fof(f50,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK4(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f406,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | spl32_2 ),
    inference(avatar_component_clause,[],[f404])).

fof(f404,plain,
    ( spl32_2
  <=> v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).

fof(f1204,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_zfmisc_1(sK0,k2_relat_1(sK1)))
    | spl32_2 ),
    inference(resolution,[],[f408,f102])).

fof(f408,plain,
    ( r2_hidden(sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | spl32_2 ),
    inference(resolution,[],[f406,f49])).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f484,plain,
    ( spl32_3
    | spl32_4
    | ~ spl32_2 ),
    inference(avatar_split_clause,[],[f220,f404,f480,f476])).

fof(f220,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f206,f39])).

fof(f39,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

fof(f206,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(resolution,[],[f151,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | sQ31_eqProxy(k7_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f42,f129])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

fof(f151,plain,(
    ~ sQ31_eqProxy(k7_relat_1(sK1,sK0),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(equality_proxy_replacement,[],[f40,f129])).

fof(f40,plain,(
    k7_relat_1(sK1,sK0) != k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f483,plain,
    ( ~ spl32_3
    | ~ spl32_4
    | ~ spl32_2 ),
    inference(avatar_split_clause,[],[f219,f404,f480,f476])).

fof(f219,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f218,f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f218,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)
    | ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f205,f39])).

fof(f205,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | ~ r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)
    | ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)
    | ~ r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(resolution,[],[f151,f154])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | sQ31_eqProxy(k7_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f41,f129])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f407,plain,
    ( spl32_1
    | ~ spl32_2 ),
    inference(avatar_split_clause,[],[f222,f404,f400])).

fof(f222,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) ),
    inference(subsumption_resolution,[],[f221,f103])).

fof(f221,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(subsumption_resolution,[],[f207,f39])).

fof(f207,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)
    | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) ),
    inference(resolution,[],[f151,f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | sQ31_eqProxy(k7_relat_1(X0,X1),X2) ) ),
    inference(equality_proxy_replacement,[],[f43,f129])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2)
      | k7_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:42:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (3215)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.18/0.51  % (3192)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.18/0.52  % (3203)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.18/0.52  % (3194)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.18/0.53  % (3194)Refutation not found, incomplete strategy% (3194)------------------------------
% 1.18/0.53  % (3194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.53  % (3194)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.53  
% 1.18/0.53  % (3194)Memory used [KB]: 10746
% 1.18/0.53  % (3194)Time elapsed: 0.113 s
% 1.18/0.53  % (3194)------------------------------
% 1.18/0.53  % (3194)------------------------------
% 1.29/0.53  % (3212)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (3199)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (3196)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.29/0.53  % (3207)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.53  % (3193)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  % (3201)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.54  % (3206)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.54  % (3195)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.54  % (3197)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.54  % (3208)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.54  % (3218)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.54  % (3200)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.54  % (3210)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.54  % (3202)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.55  % (3198)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.55  % (3204)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.55  % (3214)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.55  % (3216)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.55  % (3219)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.55  % (3211)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.55  % (3214)Refutation not found, incomplete strategy% (3214)------------------------------
% 1.29/0.55  % (3214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.55  % (3214)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.55  
% 1.29/0.55  % (3214)Memory used [KB]: 10874
% 1.29/0.55  % (3214)Time elapsed: 0.099 s
% 1.29/0.55  % (3214)------------------------------
% 1.29/0.55  % (3214)------------------------------
% 1.29/0.55  % (3213)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.55  % (3209)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.56  % (3217)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.56  % (3205)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.57  % (3221)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.57  % (3220)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.62  % (3271)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.50/0.71  % (3205)Refutation found. Thanks to Tanya!
% 2.50/0.71  % SZS status Theorem for theBenchmark
% 2.50/0.71  % (3272)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.50/0.71  % SZS output start Proof for theBenchmark
% 2.50/0.71  fof(f2169,plain,(
% 2.50/0.71    $false),
% 2.50/0.71    inference(avatar_sat_refutation,[],[f407,f483,f484,f1221,f2118,f2167])).
% 2.50/0.71  fof(f2167,plain,(
% 2.50/0.71    ~spl32_3 | spl32_4),
% 2.50/0.71    inference(avatar_contradiction_clause,[],[f2166])).
% 2.50/0.71  fof(f2166,plain,(
% 2.50/0.71    $false | (~spl32_3 | spl32_4)),
% 2.50/0.71    inference(subsumption_resolution,[],[f2150,f2135])).
% 2.50/0.71  fof(f2135,plain,(
% 2.50/0.71    ( ! [X2,X1] : (~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),X1),k2_zfmisc_1(sK0,X2))) ) | spl32_4),
% 2.50/0.71    inference(resolution,[],[f482,f90])).
% 2.50/0.71  fof(f90,plain,(
% 2.50/0.71    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 2.50/0.71    inference(cnf_transformation,[],[f12])).
% 2.50/0.71  fof(f12,axiom,(
% 2.50/0.71    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 2.50/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 2.50/0.71  fof(f482,plain,(
% 2.50/0.71    ~r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | spl32_4),
% 2.50/0.71    inference(avatar_component_clause,[],[f480])).
% 2.50/0.71  fof(f480,plain,(
% 2.50/0.71    spl32_4 <=> r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0)),
% 2.50/0.71    introduced(avatar_definition,[new_symbols(naming,[spl32_4])])).
% 2.50/0.71  fof(f2150,plain,(
% 2.50/0.71    r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k2_zfmisc_1(sK0,k2_relat_1(sK1))) | ~spl32_3),
% 2.50/0.71    inference(resolution,[],[f477,f102])).
% 2.50/0.71  fof(f102,plain,(
% 2.50/0.71    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 2.50/0.71    inference(equality_resolution,[],[f79])).
% 2.50/0.71  fof(f79,plain,(
% 2.50/0.71    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.50/0.71    inference(cnf_transformation,[],[f3])).
% 2.50/0.71  fof(f3,axiom,(
% 2.50/0.71    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.50/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.50/0.71  fof(f477,plain,(
% 2.50/0.71    r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~spl32_3),
% 2.50/0.71    inference(avatar_component_clause,[],[f476])).
% 2.50/0.71  fof(f476,plain,(
% 2.50/0.71    spl32_3 <=> r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.71    introduced(avatar_definition,[new_symbols(naming,[spl32_3])])).
% 2.50/0.71  fof(f2118,plain,(
% 2.50/0.71    ~spl32_1 | spl32_3 | ~spl32_4),
% 2.50/0.71    inference(avatar_contradiction_clause,[],[f2117])).
% 2.50/0.71  fof(f2117,plain,(
% 2.50/0.71    $false | (~spl32_1 | spl32_3 | ~spl32_4)),
% 2.50/0.71    inference(subsumption_resolution,[],[f2116,f1261])).
% 2.50/0.71  fof(f1261,plain,(
% 2.50/0.71    r2_hidden(sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_relat_1(sK1)) | ~spl32_1),
% 2.50/0.71    inference(resolution,[],[f402,f100])).
% 2.50/0.71  fof(f100,plain,(
% 2.50/0.71    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 2.50/0.71    inference(equality_resolution,[],[f67])).
% 2.50/0.71  fof(f67,plain,(
% 2.50/0.71    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 2.50/0.71    inference(cnf_transformation,[],[f19])).
% 2.50/0.71  fof(f19,axiom,(
% 2.50/0.71    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 2.50/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 2.50/0.71  fof(f402,plain,(
% 2.50/0.71    r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) | ~spl32_1),
% 2.50/0.71    inference(avatar_component_clause,[],[f400])).
% 2.50/0.71  fof(f400,plain,(
% 2.50/0.71    spl32_1 <=> r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)),
% 2.50/0.71    introduced(avatar_definition,[new_symbols(naming,[spl32_1])])).
% 2.50/0.71  fof(f2116,plain,(
% 2.50/0.71    ~r2_hidden(sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_relat_1(sK1)) | (~spl32_1 | spl32_3 | ~spl32_4)),
% 2.50/0.71    inference(subsumption_resolution,[],[f2099,f481])).
% 2.50/0.71  fof(f481,plain,(
% 2.50/0.71    r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | ~spl32_4),
% 2.50/0.71    inference(avatar_component_clause,[],[f480])).
% 2.50/0.71  fof(f2099,plain,(
% 2.50/0.71    ~r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | ~r2_hidden(sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_relat_1(sK1)) | (~spl32_1 | spl32_3)),
% 2.50/0.71    inference(resolution,[],[f1293,f105])).
% 2.50/0.71  fof(f105,plain,(
% 2.50/0.71    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 2.50/0.71    inference(equality_resolution,[],[f104])).
% 2.50/0.71  fof(f104,plain,(
% 2.50/0.71    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.50/0.71    inference(equality_resolution,[],[f88])).
% 2.50/0.71  fof(f88,plain,(
% 2.50/0.71    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.50/0.71    inference(cnf_transformation,[],[f10])).
% 2.50/0.71  fof(f10,axiom,(
% 2.50/0.71    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 2.50/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 2.50/0.71  fof(f1293,plain,(
% 2.50/0.71    ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k2_zfmisc_1(sK0,k2_relat_1(sK1))) | (~spl32_1 | spl32_3)),
% 2.50/0.71    inference(subsumption_resolution,[],[f1283,f402])).
% 2.50/0.71  fof(f1283,plain,(
% 2.50/0.71    ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) | ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k2_zfmisc_1(sK0,k2_relat_1(sK1))) | spl32_3),
% 2.50/0.71    inference(resolution,[],[f478,f101])).
% 2.50/0.71  fof(f101,plain,(
% 2.50/0.71    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 2.50/0.71    inference(equality_resolution,[],[f80])).
% 2.50/0.71  fof(f80,plain,(
% 2.50/0.71    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.50/0.71    inference(cnf_transformation,[],[f3])).
% 2.50/0.71  fof(f478,plain,(
% 2.50/0.71    ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | spl32_3),
% 2.50/0.71    inference(avatar_component_clause,[],[f476])).
% 2.50/0.71  fof(f1221,plain,(
% 2.50/0.71    spl32_2),
% 2.50/0.71    inference(avatar_contradiction_clause,[],[f1220])).
% 2.50/0.71  fof(f1220,plain,(
% 2.50/0.71    $false | spl32_2),
% 2.50/0.71    inference(subsumption_resolution,[],[f1204,f779])).
% 2.50/0.71  fof(f779,plain,(
% 2.50/0.71    ( ! [X2,X1] : (~r2_hidden(sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_zfmisc_1(X1,X2))) ) | spl32_2),
% 2.50/0.71    inference(resolution,[],[f409,f164])).
% 2.50/0.71  fof(f164,plain,(
% 2.50/0.71    ( ! [X0,X3,X1] : (sQ31_eqProxy(k4_tarski(sK17(X0,X1,X3),sK18(X0,X1,X3)),X3) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 2.50/0.71    inference(equality_proxy_replacement,[],[f106,f129])).
% 2.50/0.71  fof(f129,plain,(
% 2.50/0.71    ! [X1,X0] : (sQ31_eqProxy(X0,X1) <=> X0 = X1)),
% 2.50/0.71    introduced(equality_proxy_definition,[new_symbols(naming,[sQ31_eqProxy])])).
% 2.50/0.71  fof(f106,plain,(
% 2.50/0.71    ( ! [X0,X3,X1] : (k4_tarski(sK17(X0,X1,X3),sK18(X0,X1,X3)) = X3 | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 2.50/0.71    inference(equality_resolution,[],[f87])).
% 2.50/0.71  fof(f87,plain,(
% 2.50/0.71    ( ! [X2,X0,X3,X1] : (k4_tarski(sK17(X0,X1,X3),sK18(X0,X1,X3)) = X3 | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 2.50/0.71    inference(cnf_transformation,[],[f10])).
% 2.50/0.71  fof(f409,plain,(
% 2.50/0.71    ( ! [X0,X1] : (~sQ31_eqProxy(k4_tarski(X0,X1),sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))))) ) | spl32_2),
% 2.50/0.71    inference(resolution,[],[f406,f155])).
% 2.50/0.71  fof(f155,plain,(
% 2.50/0.71    ( ! [X2,X0,X3] : (~sQ31_eqProxy(k4_tarski(X2,X3),sK4(X0)) | v1_relat_1(X0)) )),
% 2.50/0.71    inference(equality_proxy_replacement,[],[f50,f129])).
% 2.50/0.71  fof(f50,plain,(
% 2.50/0.71    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK4(X0) | v1_relat_1(X0)) )),
% 2.50/0.71    inference(cnf_transformation,[],[f29])).
% 2.50/0.71  fof(f29,plain,(
% 2.50/0.71    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 2.50/0.71    inference(ennf_transformation,[],[f18])).
% 2.50/0.71  fof(f18,axiom,(
% 2.50/0.71    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 2.50/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 2.50/0.71  fof(f406,plain,(
% 2.50/0.71    ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | spl32_2),
% 2.50/0.71    inference(avatar_component_clause,[],[f404])).
% 2.50/0.71  fof(f404,plain,(
% 2.50/0.71    spl32_2 <=> v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.71    introduced(avatar_definition,[new_symbols(naming,[spl32_2])])).
% 2.50/0.71  fof(f1204,plain,(
% 2.50/0.71    r2_hidden(sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k2_zfmisc_1(sK0,k2_relat_1(sK1))) | spl32_2),
% 2.50/0.71    inference(resolution,[],[f408,f102])).
% 2.50/0.71  fof(f408,plain,(
% 2.50/0.71    r2_hidden(sK4(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | spl32_2),
% 2.50/0.71    inference(resolution,[],[f406,f49])).
% 2.50/0.71  fof(f49,plain,(
% 2.50/0.71    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_relat_1(X0)) )),
% 2.50/0.71    inference(cnf_transformation,[],[f29])).
% 2.50/0.71  fof(f484,plain,(
% 2.50/0.71    spl32_3 | spl32_4 | ~spl32_2),
% 2.50/0.71    inference(avatar_split_clause,[],[f220,f404,f480,f476])).
% 2.50/0.71  fof(f220,plain,(
% 2.50/0.71    ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.71    inference(subsumption_resolution,[],[f206,f39])).
% 2.50/0.71  fof(f39,plain,(
% 2.50/0.71    v1_relat_1(sK1)),
% 2.50/0.71    inference(cnf_transformation,[],[f26])).
% 2.50/0.71  fof(f26,plain,(
% 2.50/0.71    ? [X0,X1] : (k7_relat_1(X1,X0) != k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) & v1_relat_1(X1))),
% 2.50/0.71    inference(ennf_transformation,[],[f23])).
% 2.50/0.71  fof(f23,negated_conjecture,(
% 2.50/0.71    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 2.50/0.71    inference(negated_conjecture,[],[f22])).
% 2.50/0.71  fof(f22,conjecture,(
% 2.50/0.71    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 2.50/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).
% 2.50/0.72  fof(f206,plain,(
% 2.50/0.72    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(resolution,[],[f151,f153])).
% 2.50/0.72  fof(f153,plain,(
% 2.50/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | sQ31_eqProxy(k7_relat_1(X0,X1),X2)) )),
% 2.50/0.72    inference(equality_proxy_replacement,[],[f42,f129])).
% 2.50/0.72  fof(f42,plain,(
% 2.50/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k7_relat_1(X0,X1) = X2) )),
% 2.50/0.72    inference(cnf_transformation,[],[f27])).
% 2.50/0.72  fof(f27,plain,(
% 2.50/0.72    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 2.50/0.72    inference(ennf_transformation,[],[f17])).
% 2.50/0.72  fof(f17,axiom,(
% 2.50/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 2.50/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).
% 2.50/0.72  fof(f151,plain,(
% 2.50/0.72    ~sQ31_eqProxy(k7_relat_1(sK1,sK0),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(equality_proxy_replacement,[],[f40,f129])).
% 2.50/0.72  fof(f40,plain,(
% 2.50/0.72    k7_relat_1(sK1,sK0) != k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),
% 2.50/0.72    inference(cnf_transformation,[],[f26])).
% 2.50/0.72  fof(f483,plain,(
% 2.50/0.72    ~spl32_3 | ~spl32_4 | ~spl32_2),
% 2.50/0.72    inference(avatar_split_clause,[],[f219,f404,f480,f476])).
% 2.50/0.72  fof(f219,plain,(
% 2.50/0.72    ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(subsumption_resolution,[],[f218,f103])).
% 2.50/0.72  fof(f103,plain,(
% 2.50/0.72    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 2.50/0.72    inference(equality_resolution,[],[f78])).
% 2.50/0.72  fof(f78,plain,(
% 2.50/0.72    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.50/0.72    inference(cnf_transformation,[],[f3])).
% 2.50/0.72  fof(f218,plain,(
% 2.50/0.72    ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) | ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(subsumption_resolution,[],[f205,f39])).
% 2.50/0.72  fof(f205,plain,(
% 2.50/0.72    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | ~r2_hidden(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK0) | ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) | ~r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(resolution,[],[f151,f154])).
% 2.50/0.72  fof(f154,plain,(
% 2.50/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | sQ31_eqProxy(k7_relat_1(X0,X1),X2)) )),
% 2.50/0.72    inference(equality_proxy_replacement,[],[f41,f129])).
% 2.50/0.72  fof(f41,plain,(
% 2.50/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | ~r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k7_relat_1(X0,X1) = X2) )),
% 2.50/0.72    inference(cnf_transformation,[],[f27])).
% 2.50/0.72  fof(f407,plain,(
% 2.50/0.72    spl32_1 | ~spl32_2),
% 2.50/0.72    inference(avatar_split_clause,[],[f222,f404,f400])).
% 2.50/0.72  fof(f222,plain,(
% 2.50/0.72    ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1)),
% 2.50/0.72    inference(subsumption_resolution,[],[f221,f103])).
% 2.50/0.72  fof(f221,plain,(
% 2.50/0.72    ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(subsumption_resolution,[],[f207,f39])).
% 2.50/0.72  fof(f207,plain,(
% 2.50/0.72    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),sK1) | r2_hidden(k4_tarski(sK2(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1)))),sK3(sK1,sK0,k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),k3_xboole_0(sK1,k2_zfmisc_1(sK0,k2_relat_1(sK1))))),
% 2.50/0.72    inference(resolution,[],[f151,f152])).
% 2.50/0.72  fof(f152,plain,(
% 2.50/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | sQ31_eqProxy(k7_relat_1(X0,X1),X2)) )),
% 2.50/0.72    inference(equality_proxy_replacement,[],[f43,f129])).
% 2.50/0.72  fof(f43,plain,(
% 2.50/0.72    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(k4_tarski(sK2(X0,X1,X2),sK3(X0,X1,X2)),X2) | k7_relat_1(X0,X1) = X2) )),
% 2.50/0.72    inference(cnf_transformation,[],[f27])).
% 2.50/0.72  % SZS output end Proof for theBenchmark
% 2.50/0.72  % (3205)------------------------------
% 2.50/0.72  % (3205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.50/0.72  % (3205)Termination reason: Refutation
% 2.50/0.72  
% 2.50/0.72  % (3205)Memory used [KB]: 8059
% 2.50/0.72  % (3205)Time elapsed: 0.294 s
% 2.50/0.72  % (3205)------------------------------
% 2.50/0.72  % (3205)------------------------------
% 2.50/0.72  % (3188)Success in time 0.356 s
%------------------------------------------------------------------------------
