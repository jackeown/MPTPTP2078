%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 302 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :  450 (1425 expanded)
%              Number of equality atoms :   37 (  57 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1079,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f187,f191,f343,f358,f1068])).

% (29326)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f1068,plain,
    ( ~ spl9_4
    | spl9_9 ),
    inference(avatar_contradiction_clause,[],[f1067])).

fof(f1067,plain,
    ( $false
    | ~ spl9_4
    | spl9_9 ),
    inference(subsumption_resolution,[],[f1066,f336])).

fof(f336,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl9_9
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f1066,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1065,f56])).

fof(f56,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( v3_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( v3_tex_2(X1,sK4)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
        & v1_xboole_0(X1) )
   => ( v3_tex_2(sK5,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
      & v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f1065,plain,
    ( v2_struct_0(sK4)
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1064,f57])).

fof(f57,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f1064,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f1047,f58])).

fof(f58,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f1047,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(resolution,[],[f1045,f198])).

fof(f198,plain,
    ( sP0(k1_xboole_0,sK4)
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f126,f186])).

fof(f186,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_4
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f126,plain,(
    sP0(sK5,sK4) ),
    inference(resolution,[],[f125,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | sP0(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( sP1(X0,X1)
        | ~ sP0(X1,X0)
        | ~ v2_tex_2(X1,X0) )
      & ( ( sP0(X1,X0)
          & v2_tex_2(X1,X0) )
        | ~ sP1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
    <=> ( sP0(X1,X0)
        & v2_tex_2(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f125,plain,(
    sP1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f124,f61])).

fof(f61,plain,(
    v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f124,plain,
    ( ~ v3_tex_2(sK5,sK4)
    | sP1(sK4,sK5) ),
    inference(resolution,[],[f122,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1)
      | ~ v3_tex_2(X0,X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v3_tex_2(X0,X1)
          | ~ sP1(X1,X0) )
        & ( sP1(X1,X0)
          | ~ v3_tex_2(X0,X1) ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ( ( v3_tex_2(X1,X0)
          | ~ sP1(X0,X1) )
        & ( sP1(X0,X1)
          | ~ v3_tex_2(X1,X0) ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ( v3_tex_2(X1,X0)
      <=> sP1(X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f122,plain,(
    sP2(sK5,sK4) ),
    inference(subsumption_resolution,[],[f118,f58])).

fof(f118,plain,
    ( sP2(sK5,sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f75,f60])).

fof(f60,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | sP2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f20,f36,f35,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ! [X2] :
          ( X1 = X2
          | ~ r1_tarski(X1,X2)
          | ~ v2_tex_2(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f1045,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f1043,f93])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 != k1_tarski(X0) ),
    inference(superposition,[],[f84,f64])).

fof(f64,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f84,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f1043,plain,(
    ! [X0] :
      ( ~ sP0(k1_xboole_0,X0)
      | k1_xboole_0 = k1_tarski(sK8(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f769,f62])).

fof(f62,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f769,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X14,k1_tarski(sK8(u1_struct_0(X13))))
      | ~ sP0(X14,X13)
      | k1_tarski(sK8(u1_struct_0(X13))) = X14
      | ~ l1_pre_topc(X13)
      | ~ v2_pre_topc(X13)
      | v2_struct_0(X13)
      | v1_xboole_0(u1_struct_0(X13)) ) ),
    inference(resolution,[],[f320,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(sK8(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f5,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK8(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X2))
      | k1_tarski(X1) = X0
      | ~ sP0(X0,X2)
      | ~ r1_tarski(X0,k1_tarski(X1))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f317,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | ~ sP0(X0,X2)
      | ~ r2_hidden(X1,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v2_struct_0(X2)
      | v1_xboole_0(u1_struct_0(X2)) ) ),
    inference(resolution,[],[f168,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k1_tarski(X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k1_tarski(X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(superposition,[],[f78,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f168,plain,(
    ! [X6,X7,X5] :
      ( ~ v2_tex_2(k1_tarski(X6),X7)
      | ~ r1_tarski(X5,k1_tarski(X6))
      | k1_tarski(X6) = X5
      | ~ sP0(X5,X7)
      | ~ r2_hidden(X6,u1_struct_0(X7)) ) ),
    inference(resolution,[],[f70,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r1_tarski(X0,X3)
      | ~ v2_tex_2(X3,X1)
      | X0 = X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK6(X0,X1) != X0
          & r1_tarski(X0,sK6(X0,X1))
          & v2_tex_2(sK6(X0,X1),X1)
          & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X0 != X2
          & r1_tarski(X0,X2)
          & v2_tex_2(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( sK6(X0,X1) != X0
        & r1_tarski(X0,sK6(X0,X1))
        & v2_tex_2(sK6(X0,X1),X1)
        & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( X0 != X2
            & r1_tarski(X0,X2)
            & v2_tex_2(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( X0 = X3
            | ~ r1_tarski(X0,X3)
            | ~ v2_tex_2(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2] :
            ( X1 != X2
            & r1_tarski(X1,X2)
            & v2_tex_2(X2,X0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
      & ( ! [X2] :
            ( X1 = X2
            | ~ r1_tarski(X1,X2)
            | ~ v2_tex_2(X2,X0)
            | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f358,plain,(
    spl9_7 ),
    inference(avatar_contradiction_clause,[],[f357])).

fof(f357,plain,
    ( $false
    | spl9_7 ),
    inference(subsumption_resolution,[],[f356,f56])).

fof(f356,plain,
    ( v2_struct_0(sK4)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f355,f57])).

fof(f355,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f354,f58])).

fof(f354,plain,
    ( ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | spl9_7 ),
    inference(resolution,[],[f309,f82])).

fof(f82,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f26,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP3(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).

fof(f309,plain,
    ( ~ sP3(sK4)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl9_7
  <=> sP3(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f343,plain,
    ( ~ spl9_7
    | ~ spl9_9 ),
    inference(avatar_split_clause,[],[f342,f335,f307])).

fof(f342,plain,
    ( ~ sP3(sK4)
    | ~ spl9_9 ),
    inference(resolution,[],[f337,f109])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ sP3(X0) ) ),
    inference(subsumption_resolution,[],[f108,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK7(X0))
      | ~ sP3(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v4_pre_topc(sK7(X0),X0)
        & ~ v1_xboole_0(sK7(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP3(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v4_pre_topc(sK7(X0),X0)
        & ~ v1_xboole_0(sK7(X0))
        & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ sP3(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f108,plain,(
    ! [X0] :
      ( ~ sP3(X0)
      | v1_xboole_0(sK7(X0))
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(resolution,[],[f79,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ sP3(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f337,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f335])).

fof(f191,plain,(
    spl9_3 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | spl9_3 ),
    inference(subsumption_resolution,[],[f189,f59])).

fof(f59,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f42])).

fof(f189,plain,
    ( ~ v1_xboole_0(sK5)
    | spl9_3 ),
    inference(resolution,[],[f188,f61])).

fof(f188,plain,
    ( ! [X0] :
        ( ~ v3_tex_2(X0,sK4)
        | ~ v1_xboole_0(X0) )
    | spl9_3 ),
    inference(superposition,[],[f182,f76])).

fof(f76,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f182,plain,
    ( ~ v3_tex_2(k1_xboole_0,sK4)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl9_3
  <=> v3_tex_2(k1_xboole_0,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f187,plain,
    ( ~ spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f178,f184,f180])).

fof(f178,plain,
    ( k1_xboole_0 = sK5
    | ~ v3_tex_2(k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f177,f58])).

fof(f177,plain,
    ( k1_xboole_0 = sK5
    | ~ l1_pre_topc(sK4)
    | ~ v3_tex_2(k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f176,f62])).

fof(f176,plain,
    ( k1_xboole_0 = sK5
    | ~ r1_tarski(k1_xboole_0,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v3_tex_2(k1_xboole_0,sK4) ),
    inference(resolution,[],[f173,f150])).

fof(f150,plain,(
    ! [X1] :
      ( sP0(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v3_tex_2(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f129,f68])).

% (29308)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f129,plain,(
    ! [X1] :
      ( sP1(X1,k1_xboole_0)
      | ~ v3_tex_2(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f116,f65])).

fof(f116,plain,(
    ! [X2] :
      ( sP2(k1_xboole_0,X2)
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f75,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f173,plain,(
    ! [X8] :
      ( ~ sP0(X8,sK4)
      | sK5 = X8
      | ~ r1_tarski(X8,sK5) ) ),
    inference(subsumption_resolution,[],[f169,f127])).

fof(f127,plain,(
    v2_tex_2(sK5,sK4) ),
    inference(resolution,[],[f125,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f169,plain,(
    ! [X8] :
      ( ~ r1_tarski(X8,sK5)
      | ~ v2_tex_2(sK5,sK4)
      | sK5 = X8
      | ~ sP0(X8,sK4) ) ),
    inference(resolution,[],[f70,f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:53:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (29325)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (29303)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (29304)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (29305)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (29307)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (29307)Refutation not found, incomplete strategy% (29307)------------------------------
% 0.21/0.51  % (29307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (29307)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (29307)Memory used [KB]: 6140
% 0.21/0.51  % (29307)Time elapsed: 0.086 s
% 0.21/0.51  % (29307)------------------------------
% 0.21/0.51  % (29307)------------------------------
% 0.21/0.51  % (29314)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (29309)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (29329)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (29317)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (29316)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (29316)Refutation not found, incomplete strategy% (29316)------------------------------
% 0.21/0.52  % (29316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29316)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29316)Memory used [KB]: 6140
% 0.21/0.52  % (29316)Time elapsed: 0.095 s
% 0.21/0.52  % (29316)------------------------------
% 0.21/0.52  % (29316)------------------------------
% 0.21/0.52  % (29323)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (29311)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (29302)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (29313)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (29315)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (29305)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (29322)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (29324)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (29321)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (29327)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (29301)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (29301)Refutation not found, incomplete strategy% (29301)------------------------------
% 0.21/0.54  % (29301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (29301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (29301)Memory used [KB]: 10618
% 0.21/0.54  % (29301)Time elapsed: 0.115 s
% 0.21/0.54  % (29301)------------------------------
% 0.21/0.54  % (29301)------------------------------
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1079,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f187,f191,f343,f358,f1068])).
% 0.21/0.54  % (29326)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  fof(f1068,plain,(
% 0.21/0.54    ~spl9_4 | spl9_9),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1067])).
% 0.21/0.54  fof(f1067,plain,(
% 0.21/0.54    $false | (~spl9_4 | spl9_9)),
% 0.21/0.54    inference(subsumption_resolution,[],[f1066,f336])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    ~v1_xboole_0(u1_struct_0(sK4)) | spl9_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f335])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    spl9_9 <=> v1_xboole_0(u1_struct_0(sK4))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 0.21/0.54  fof(f1066,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK4)) | ~spl9_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f1065,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ~v2_struct_0(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    (v3_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f18,f41,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ? [X1] : (v3_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) => (v3_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f15])).
% 0.21/0.54  fof(f15,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.21/0.54  fof(f1065,plain,(
% 0.21/0.54    v2_struct_0(sK4) | v1_xboole_0(u1_struct_0(sK4)) | ~spl9_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f1064,f57])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    v2_pre_topc(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f1064,plain,(
% 0.21/0.54    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | v1_xboole_0(u1_struct_0(sK4)) | ~spl9_4),
% 0.21/0.54    inference(subsumption_resolution,[],[f1047,f58])).
% 0.21/0.54  fof(f58,plain,(
% 0.21/0.54    l1_pre_topc(sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f1047,plain,(
% 0.21/0.54    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | v1_xboole_0(u1_struct_0(sK4)) | ~spl9_4),
% 0.21/0.54    inference(resolution,[],[f1045,f198])).
% 0.21/0.54  fof(f198,plain,(
% 0.21/0.54    sP0(k1_xboole_0,sK4) | ~spl9_4),
% 0.21/0.54    inference(backward_demodulation,[],[f126,f186])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~spl9_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f184])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl9_4 <=> k1_xboole_0 = sK5),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    sP0(sK5,sK4)),
% 0.21/0.54    inference(resolution,[],[f125,f68])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP1(X0,X1) | sP0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP1(X0,X1) | ~sP0(X1,X0) | ~v2_tex_2(X1,X0)) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP1(X0,X1) | (~sP0(X1,X0) | ~v2_tex_2(X1,X0))) & ((sP0(X1,X0) & v2_tex_2(X1,X0)) | ~sP1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : (sP1(X0,X1) <=> (sP0(X1,X0) & v2_tex_2(X1,X0)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    sP1(sK4,sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f124,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    v3_tex_2(sK5,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f124,plain,(
% 0.21/0.54    ~v3_tex_2(sK5,sK4) | sP1(sK4,sK5)),
% 0.21/0.54    inference(resolution,[],[f122,f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP2(X0,X1) | ~v3_tex_2(X0,X1) | sP1(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1] : (((v3_tex_2(X0,X1) | ~sP1(X1,X0)) & (sP1(X1,X0) | ~v3_tex_2(X0,X1))) | ~sP2(X0,X1))),
% 0.21/0.54    inference(rectify,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X1,X0] : (((v3_tex_2(X1,X0) | ~sP1(X0,X1)) & (sP1(X0,X1) | ~v3_tex_2(X1,X0))) | ~sP2(X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X1,X0] : ((v3_tex_2(X1,X0) <=> sP1(X0,X1)) | ~sP2(X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    sP2(sK5,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f118,f58])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    sP2(sK5,sK4) | ~l1_pre_topc(sK4)),
% 0.21/0.54    inference(resolution,[],[f75,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | sP2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(definition_folding,[],[f20,f36,f35,f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ! [X1,X0] : (sP0(X1,X0) <=> ! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.54  fof(f1045,plain,(
% 0.21/0.54    ( ! [X0] : (~sP0(k1_xboole_0,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f1043,f93])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 != k1_tarski(X0)) )),
% 0.21/0.54    inference(superposition,[],[f84,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.54  fof(f1043,plain,(
% 0.21/0.54    ( ! [X0] : (~sP0(k1_xboole_0,X0) | k1_xboole_0 = k1_tarski(sK8(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.54    inference(resolution,[],[f769,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.54  fof(f769,plain,(
% 0.21/0.54    ( ! [X14,X13] : (~r1_tarski(X14,k1_tarski(sK8(u1_struct_0(X13)))) | ~sP0(X14,X13) | k1_tarski(sK8(u1_struct_0(X13))) = X14 | ~l1_pre_topc(X13) | ~v2_pre_topc(X13) | v2_struct_0(X13) | v1_xboole_0(u1_struct_0(X13))) )),
% 0.21/0.54    inference(resolution,[],[f320,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK8(X0),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0] : m1_subset_1(sK8(X0),X0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f5,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK8(X0),X0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X2)) | k1_tarski(X1) = X0 | ~sP0(X0,X2) | ~r1_tarski(X0,k1_tarski(X1)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_xboole_0(u1_struct_0(X2))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f317,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f317,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | ~sP0(X0,X2) | ~r2_hidden(X1,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v2_struct_0(X2) | v1_xboole_0(u1_struct_0(X2))) )),
% 0.21/0.54    inference(resolution,[],[f168,f157])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_tex_2(k1_tarski(X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f156])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_tex_2(k1_tarski(X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.54    inference(superposition,[],[f78,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (~v2_tex_2(k1_tarski(X6),X7) | ~r1_tarski(X5,k1_tarski(X6)) | k1_tarski(X6) = X5 | ~sP0(X5,X7) | ~r2_hidden(X6,u1_struct_0(X7))) )),
% 0.21/0.54    inference(resolution,[],[f70,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | X0 = X3 | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f50])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP0(X0,X1) | (sK6(X0,X1) != X0 & r1_tarski(X0,sK6(X0,X1)) & v2_tex_2(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f48,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (sK6(X0,X1) != X0 & r1_tarski(X0,sK6(X0,X1)) & v2_tex_2(sK6(X0,X1),X1) & m1_subset_1(sK6(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : (X0 != X2 & r1_tarski(X0,X2) & v2_tex_2(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (X0 = X3 | ~r1_tarski(X0,X3) | ~v2_tex_2(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~sP0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ! [X1,X0] : ((sP0(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP0(X1,X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f34])).
% 0.21/0.54  fof(f358,plain,(
% 0.21/0.54    spl9_7),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f357])).
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    $false | spl9_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f356,f56])).
% 0.21/0.54  fof(f356,plain,(
% 0.21/0.54    v2_struct_0(sK4) | spl9_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f355,f57])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl9_7),
% 0.21/0.54    inference(subsumption_resolution,[],[f354,f58])).
% 0.21/0.54  fof(f354,plain,(
% 0.21/0.54    ~l1_pre_topc(sK4) | ~v2_pre_topc(sK4) | v2_struct_0(sK4) | spl9_7),
% 0.21/0.54    inference(resolution,[],[f309,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0] : (sP3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0] : (sP3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(definition_folding,[],[f26,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc7_pre_topc)).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    ~sP3(sK4) | spl9_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f307])).
% 0.21/0.54  fof(f307,plain,(
% 0.21/0.54    spl9_7 <=> sP3(sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.54  fof(f343,plain,(
% 0.21/0.54    ~spl9_7 | ~spl9_9),
% 0.21/0.54    inference(avatar_split_clause,[],[f342,f335,f307])).
% 0.21/0.54  fof(f342,plain,(
% 0.21/0.54    ~sP3(sK4) | ~spl9_9),
% 0.21/0.54    inference(resolution,[],[f337,f109])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~sP3(X0)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f108,f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(sK7(X0)) | ~sP3(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0] : ((v4_pre_topc(sK7(X0),X0) & ~v1_xboole_0(sK7(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f51,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v4_pre_topc(sK7(X0),X0) & ~v1_xboole_0(sK7(X0)) & m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~sP3(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f38])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ( ! [X0] : (~sP3(X0) | v1_xboole_0(sK7(X0)) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.54    inference(resolution,[],[f79,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~sP3(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f53])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK4)) | ~spl9_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f335])).
% 0.21/0.54  fof(f191,plain,(
% 0.21/0.54    spl9_3),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.54  fof(f190,plain,(
% 0.21/0.54    $false | spl9_3),
% 0.21/0.54    inference(subsumption_resolution,[],[f189,f59])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    v1_xboole_0(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f189,plain,(
% 0.21/0.54    ~v1_xboole_0(sK5) | spl9_3),
% 0.21/0.54    inference(resolution,[],[f188,f61])).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X0] : (~v3_tex_2(X0,sK4) | ~v1_xboole_0(X0)) ) | spl9_3),
% 0.21/0.54    inference(superposition,[],[f182,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.54  fof(f182,plain,(
% 0.21/0.54    ~v3_tex_2(k1_xboole_0,sK4) | spl9_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f180])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    spl9_3 <=> v3_tex_2(k1_xboole_0,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.54  fof(f187,plain,(
% 0.21/0.54    ~spl9_3 | spl9_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f178,f184,f180])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~v3_tex_2(k1_xboole_0,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f177,f58])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~l1_pre_topc(sK4) | ~v3_tex_2(k1_xboole_0,sK4)),
% 0.21/0.54    inference(subsumption_resolution,[],[f176,f62])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~r1_tarski(k1_xboole_0,sK5) | ~l1_pre_topc(sK4) | ~v3_tex_2(k1_xboole_0,sK4)),
% 0.21/0.54    inference(resolution,[],[f173,f150])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ( ! [X1] : (sP0(k1_xboole_0,X1) | ~l1_pre_topc(X1) | ~v3_tex_2(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(resolution,[],[f129,f68])).
% 0.21/0.55  % (29308)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ( ! [X1] : (sP1(X1,k1_xboole_0) | ~v3_tex_2(k1_xboole_0,X1) | ~l1_pre_topc(X1)) )),
% 0.21/0.55    inference(resolution,[],[f116,f65])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    ( ! [X2] : (sP2(k1_xboole_0,X2) | ~l1_pre_topc(X2)) )),
% 0.21/0.55    inference(resolution,[],[f75,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.55  fof(f173,plain,(
% 0.21/0.55    ( ! [X8] : (~sP0(X8,sK4) | sK5 = X8 | ~r1_tarski(X8,sK5)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f169,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    v2_tex_2(sK5,sK4)),
% 0.21/0.55    inference(resolution,[],[f125,f67])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~sP1(X0,X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f46])).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    ( ! [X8] : (~r1_tarski(X8,sK5) | ~v2_tex_2(sK5,sK4) | sK5 = X8 | ~sP0(X8,sK4)) )),
% 0.21/0.55    inference(resolution,[],[f70,f60])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (29305)------------------------------
% 0.21/0.55  % (29305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (29305)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (29305)Memory used [KB]: 6652
% 0.21/0.55  % (29305)Time elapsed: 0.090 s
% 0.21/0.55  % (29305)------------------------------
% 0.21/0.55  % (29305)------------------------------
% 0.21/0.55  % (29297)Success in time 0.181 s
%------------------------------------------------------------------------------
