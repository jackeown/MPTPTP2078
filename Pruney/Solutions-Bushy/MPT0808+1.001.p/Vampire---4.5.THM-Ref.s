%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0808+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 154 expanded)
%              Number of leaves         :   14 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  234 ( 803 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f66,f80,f88,f94,f100,f102,f113,f127,f148,f165])).

fof(f165,plain,(
    spl5_9 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl5_9 ),
    inference(resolution,[],[f163,f20])).

fof(f20,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                      | ~ r2_hidden(X4,k3_relat_1(X1)) )
                  & r2_hidden(X3,k3_relat_1(X0)) )
              & r3_wellord1(X0,X1,X2)
              & v2_wellord1(X0)
              & v1_funct_1(X2)
              & v1_relat_1(X2) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( r3_wellord1(X0,X1,X2)
                    & v2_wellord1(X0) )
                 => ! [X3] :
                      ~ ( ! [X4] :
                            ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                              & r2_hidden(X4,k3_relat_1(X1)) )
                        & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( r3_wellord1(X0,X1,X2)
                  & v2_wellord1(X0) )
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_wellord1)).

fof(f163,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_9 ),
    inference(resolution,[],[f123,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f123,plain,
    ( ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl5_9
  <=> r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f148,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl5_10 ),
    inference(resolution,[],[f126,f17])).

fof(f17,plain,(
    v2_wellord1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f126,plain,
    ( ~ v2_wellord1(sK0)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_10
  <=> v2_wellord1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f127,plain,
    ( ~ spl5_3
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_2 ),
    inference(avatar_split_clause,[],[f120,f42,f64,f61,f58,f125,f122,f55,f49])).

fof(f49,plain,
    ( spl5_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f55,plain,
    ( spl5_5
  <=> r3_wellord1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f58,plain,
    ( spl5_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f61,plain,
    ( spl5_7
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f64,plain,
    ( spl5_8
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f42,plain,
    ( spl5_2
  <=> r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f120,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_wellord1(sK0)
    | ~ r1_tarski(k1_wellord1(sK0,sK3),k3_relat_1(sK0))
    | ~ r3_wellord1(sK0,sK1,sK2)
    | ~ v1_relat_1(sK0)
    | spl5_2 ),
    inference(resolution,[],[f43,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | ~ v1_funct_1(X3)
      | ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ r3_wellord1(X1,X2,X3)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) )
              | ~ r3_wellord1(X1,X2,X3)
              | ~ r1_tarski(X0,k3_relat_1(X1))
              | ~ v2_wellord1(X1)
              | ~ v1_funct_1(X3)
              | ~ v1_relat_1(X3) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_relat_1(X3) )
             => ( ( r3_wellord1(X1,X2,X3)
                  & r1_tarski(X0,k3_relat_1(X1))
                  & v2_wellord1(X1) )
               => ( r4_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)))
                  & r3_wellord1(k2_wellord1(X1,X0),k2_wellord1(X2,k9_relat_1(X3,X0)),k7_relat_1(X3,X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_wellord1)).

fof(f43,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f113,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f56,f18])).

fof(f18,plain,(
    r3_wellord1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f56,plain,
    ( ~ r3_wellord1(sK0,sK1,sK2)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f102,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f53,f14])).

fof(f14,plain,(
    r2_hidden(sK3,k3_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( ~ r2_hidden(sK3,k3_relat_1(sK0))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_4
  <=> r2_hidden(sK3,k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f100,plain,(
    spl5_8 ),
    inference(avatar_contradiction_clause,[],[f99])).

fof(f99,plain,
    ( $false
    | spl5_8 ),
    inference(resolution,[],[f65,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,
    ( ~ v1_relat_1(sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f64])).

fof(f94,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl5_7 ),
    inference(resolution,[],[f62,f15])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f62,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f88,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | spl5_6 ),
    inference(resolution,[],[f59,f16])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f59,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f80,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f50,f20])).

fof(f50,plain,
    ( ~ v1_relat_1(sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f66,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | spl5_1 ),
    inference(avatar_split_clause,[],[f47,f39,f64,f61,f58,f55,f52,f49])).

fof(f39,plain,
    ( spl5_1
  <=> r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f47,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r3_wellord1(sK0,sK1,sK2)
    | ~ r2_hidden(sK3,k3_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | spl5_1 ),
    inference(resolution,[],[f40,f21])).

fof(f21,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK4(X0,X1,X2,X3),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r3_wellord1(X0,X1,X2)
      | ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                      & r2_hidden(X4,k3_relat_1(X1)) )
                  | ~ r2_hidden(X3,k3_relat_1(X0)) )
              | ~ r3_wellord1(X0,X1,X2)
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( r3_wellord1(X0,X1,X2)
               => ! [X3] :
                    ~ ( ! [X4] :
                          ~ ( k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,X4)
                            & r2_hidden(X4,k3_relat_1(X1)) )
                      & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_wellord1)).

fof(f40,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f44,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f36,f42,f39])).

fof(f36,plain,
    ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k9_relat_1(sK2,k1_wellord1(sK0,sK3))))
    | ~ r2_hidden(sK4(sK0,sK1,sK2,sK3),k3_relat_1(sK1)) ),
    inference(superposition,[],[f13,f32])).

fof(f32,plain,(
    k9_relat_1(sK2,k1_wellord1(sK0,sK3)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,sK3)) ),
    inference(resolution,[],[f31,f14])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) ) ),
    inference(global_subsumption,[],[f15,f16,f19,f20,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(sK0))
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK1)
      | ~ v1_relat_1(sK0)
      | k9_relat_1(sK2,k1_wellord1(sK0,X0)) = k1_wellord1(sK1,sK4(sK0,sK1,sK2,X0)) ) ),
    inference(resolution,[],[f22,f18])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_relat_1(X0))
      | ~ r3_wellord1(X0,X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k9_relat_1(X2,k1_wellord1(X0,X3)) = k1_wellord1(X1,sK4(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,plain,(
    ! [X4] :
      ( ~ r4_wellord1(k2_wellord1(sK0,k1_wellord1(sK0,sK3)),k2_wellord1(sK1,k1_wellord1(sK1,X4)))
      | ~ r2_hidden(X4,k3_relat_1(sK1)) ) ),
    inference(cnf_transformation,[],[f7])).

%------------------------------------------------------------------------------
