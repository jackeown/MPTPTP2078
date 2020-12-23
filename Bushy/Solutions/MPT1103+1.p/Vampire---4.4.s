%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : pre_topc__t23_pre_topc.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:29 EDT 2019

% Result     : Theorem 0.73s
% Output     : Refutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 194 expanded)
%              Number of leaves         :   17 (  67 expanded)
%              Depth                    :   12
%              Number of atoms          :  206 ( 804 expanded)
%              Number of equality atoms :   77 ( 468 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f100,f165,f197,f264,f266,f355])).

fof(f355,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f345,f294])).

fof(f294,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK1)
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f152,f135])).

fof(f135,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f106,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',t37_xboole_1)).

fof(f106,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f55,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',t3_subset)).

fof(f55,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ( k2_struct_0(sK0) = sK1
        & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0 )
      | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
        & k2_struct_0(sK0) != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k2_struct_0(X0) = X1
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
              | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
                & k2_struct_0(X0) != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k2_struct_0(sK0) = X1
              & k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) != k1_xboole_0 )
            | ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X1) = k1_xboole_0
              & k2_struct_0(sK0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k2_struct_0(X0) = sK1
            & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) != k1_xboole_0 )
          | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),sK1) = k1_xboole_0
            & k2_struct_0(X0) != sK1 ) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k2_struct_0(X0) = X1
              & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
            | ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
              & k2_struct_0(X0) != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k2_struct_0(X0) = X1
                  & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
              & ~ ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
                  & k2_struct_0(X0) != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) != k1_xboole_0 )
            & ~ ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) = k1_xboole_0
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',t23_pre_topc)).

fof(f152,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f101,f98])).

fof(f98,plain,
    ( k2_struct_0(sK0) = sK1
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_2
  <=> k2_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f101,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',d3_struct_0)).

fof(f54,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f345,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK1)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(superposition,[],[f315,f271])).

fof(f271,plain,
    ( ! [X1] : k7_subset_1(sK1,sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl5_2 ),
    inference(resolution,[],[f156,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',redefinition_k7_subset_1)).

fof(f156,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f152,f55])).

fof(f315,plain,
    ( k7_subset_1(sK1,sK1,sK1) != k1_xboole_0
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f151,f152])).

fof(f151,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,sK1) != k1_xboole_0
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f89,f98])).

fof(f89,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl5_1
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f266,plain,
    ( spl5_3
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f149,f172])).

fof(f172,plain,
    ( u1_struct_0(sK0) != sK1
    | ~ spl5_3 ),
    inference(superposition,[],[f95,f101])).

fof(f95,plain,
    ( k2_struct_0(sK0) != sK1
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_3
  <=> k2_struct_0(sK0) != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f149,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl5_14
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f264,plain,
    ( ~ spl5_0
    | spl5_13
    | ~ spl5_16 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f262,f143])).

fof(f143,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl5_13
  <=> ~ r1_tarski(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f262,plain,
    ( r1_tarski(u1_struct_0(sK0),sK1)
    | ~ spl5_0
    | ~ spl5_16 ),
    inference(trivial_inequality_removal,[],[f261])).

fof(f261,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(u1_struct_0(sK0),sK1)
    | ~ spl5_0
    | ~ spl5_16 ),
    inference(superposition,[],[f74,f257])).

fof(f257,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_0
    | ~ spl5_16 ),
    inference(superposition,[],[f206,f179])).

fof(f179,plain,
    ( k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl5_0 ),
    inference(forward_demodulation,[],[f92,f101])).

fof(f92,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl5_0
  <=> k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f206,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),X1) = k4_xboole_0(u1_struct_0(sK0),X1)
    | ~ spl5_16 ),
    inference(resolution,[],[f183,f79])).

fof(f183,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl5_16
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f197,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f174,f186])).

fof(f186,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl5_17
  <=> ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f174,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f173,f54])).

fof(f173,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f64,f101])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',dt_k2_struct_0)).

fof(f165,plain,
    ( ~ spl5_13
    | spl5_14 ),
    inference(avatar_split_clause,[],[f164,f148,f142])).

fof(f164,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r1_tarski(u1_struct_0(sK0),sK1) ),
    inference(resolution,[],[f106,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/pre_topc__t23_pre_topc.p',d10_xboole_0)).

fof(f100,plain,
    ( ~ spl5_3
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f56,f88,f94])).

fof(f56,plain,
    ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != k1_xboole_0
    | k2_struct_0(sK0) != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,
    ( spl5_0
    | spl5_2 ),
    inference(avatar_split_clause,[],[f59,f97,f91])).

fof(f59,plain,
    ( k2_struct_0(sK0) = sK1
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
