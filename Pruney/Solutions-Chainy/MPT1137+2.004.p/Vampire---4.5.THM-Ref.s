%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  118 (2291 expanded)
%              Number of leaves         :   20 ( 810 expanded)
%              Depth                    :   24
%              Number of atoms          :  377 (13622 expanded)
%              Number of equality atoms :   40 (1989 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f472,plain,(
    $false ),
    inference(subsumption_resolution,[],[f471,f437])).

fof(f437,plain,(
    r2_hidden(sK3,k1_xboole_0) ),
    inference(resolution,[],[f403,f70])).

fof(f70,plain,(
    ! [X0] : m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(sK7(X0),k1_zfmisc_1(X0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f403,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_xboole_0))
      | r2_hidden(sK3,k1_xboole_0) ) ),
    inference(resolution,[],[f395,f235])).

fof(f235,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f212,f207])).

fof(f207,plain,(
    k1_xboole_0 = u1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f206,f131])).

fof(f131,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(resolution,[],[f86,f68])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f86,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f48,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f48,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK3 != sK4
    & r1_orders_2(sK2,sK4,sK3)
    & r1_orders_2(sK2,sK3,sK4)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( X1 != X2
                & r1_orders_2(X0,X2,X1)
                & r1_orders_2(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(sK2,X2,X1)
              & r1_orders_2(sK2,X1,X2)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( X1 != X2
            & r1_orders_2(sK2,X2,X1)
            & r1_orders_2(sK2,X1,X2)
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( sK3 != X2
          & r1_orders_2(sK2,X2,sK3)
          & r1_orders_2(sK2,sK3,X2)
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( sK3 != X2
        & r1_orders_2(sK2,X2,sK3)
        & r1_orders_2(sK2,sK3,X2)
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( sK3 != sK4
      & r1_orders_2(sK2,sK4,sK3)
      & r1_orders_2(sK2,sK3,sK4)
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( X1 != X2
              & r1_orders_2(X0,X2,X1)
              & r1_orders_2(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X1)
                    & r1_orders_2(X0,X1,X2) )
                 => X1 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).

fof(f206,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f202,f150])).

fof(f150,plain,(
    sP0(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f148,f109])).

fof(f109,plain,
    ( ~ sP1(u1_orders_2(sK2))
    | sP0(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    inference(resolution,[],[f81,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ r4_relat_2(X0,X1)
      | ~ sP1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r4_relat_2(X0,X1)
            | ~ sP0(X0,X1) )
          & ( sP0(X0,X1)
            | ~ r4_relat_2(X0,X1) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> sP0(X0,X1) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f81,plain,(
    r4_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f78,f46])).

fof(f46,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,
    ( r4_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))
    | ~ v5_orders_2(sK2) ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v5_orders_2(X0)
          | ~ r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v5_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
      <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).

fof(f47,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f148,plain,(
    sP1(u1_orders_2(sK2)) ),
    inference(resolution,[],[f147,f67])).

fof(f67,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f23,f31,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( X2 = X3
          | ~ r2_hidden(k4_tarski(X3,X2),X0)
          | ~ r2_hidden(k4_tarski(X2,X3),X0)
          | ~ r2_hidden(X3,X1)
          | ~ r2_hidden(X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( X2 = X3
              | ~ r2_hidden(k4_tarski(X3,X2),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r4_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X3,X2),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).

fof(f147,plain,(
    v1_relat_1(u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f145,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f145,plain,
    ( v1_relat_1(u1_orders_2(sK2))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    inference(resolution,[],[f80,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f80,plain,(
    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f202,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ sP0(u1_orders_2(sK2),u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(resolution,[],[f125,f135])).

fof(f135,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(resolution,[],[f95,f68])).

fof(f95,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(resolution,[],[f49,f73])).

fof(f49,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ r2_hidden(sK3,X0)
      | ~ sP0(u1_orders_2(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f124,f103])).

fof(f103,plain,(
    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f102,f47])).

fof(f102,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f101,f48])).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f100,f49])).

fof(f100,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f50,plain,(
    r1_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
      | ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ sP0(u1_orders_2(sK2),X0) ) ),
    inference(subsumption_resolution,[],[f119,f52])).

fof(f52,plain,(
    sK3 != sK4 ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    ! [X0] :
      ( sK3 = sK4
      | ~ r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))
      | ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK4,X0)
      | ~ sP0(u1_orders_2(sK2),X0) ) ),
    inference(resolution,[],[f107,f61])).

fof(f61,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X5,X4),X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( sK5(X0,X1) != sK6(X0,X1)
          & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
          & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
          & r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( X2 != X3
          & r2_hidden(k4_tarski(X3,X2),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( sK5(X0,X1) != sK6(X0,X1)
        & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | ~ r2_hidden(k4_tarski(X5,X4),X0)
            | ~ r2_hidden(k4_tarski(X4,X5),X0)
            | ~ r2_hidden(X5,X1)
            | ~ r2_hidden(X4,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( X2 != X3
            & r2_hidden(k4_tarski(X3,X2),X0)
            & r2_hidden(k4_tarski(X2,X3),X0)
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) ) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f107,plain,(
    r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) ),
    inference(subsumption_resolution,[],[f106,f47])).

fof(f106,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f105,f49])).

fof(f105,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f104,f48])).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f51,f56])).

fof(f51,plain,(
    r1_orders_2(sK2,sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f212,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f86,f207])).

fof(f395,plain,(
    ! [X6,X5] :
      ( ~ v1_xboole_0(X6)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6)) ) ),
    inference(subsumption_resolution,[],[f392,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f392,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK3,sK4),X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(X6))
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f327,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f327,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | r2_hidden(k4_tarski(sK3,sK4),X0) ) ),
    inference(superposition,[],[f261,f68])).

fof(f261,plain,(
    r2_hidden(k4_tarski(sK3,sK4),k1_xboole_0) ),
    inference(backward_demodulation,[],[f103,f205])).

fof(f205,plain,(
    k1_xboole_0 = u1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f204,f166])).

fof(f166,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | k1_xboole_0 = u1_orders_2(sK2) ),
    inference(resolution,[],[f159,f86])).

fof(f159,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | k1_xboole_0 = u1_orders_2(sK2) ),
    inference(resolution,[],[f142,f68])).

fof(f142,plain,
    ( v1_xboole_0(u1_orders_2(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f80,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f204,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | k1_xboole_0 = u1_orders_2(sK2) ),
    inference(subsumption_resolution,[],[f201,f150])).

fof(f201,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | ~ sP0(u1_orders_2(sK2),u1_struct_0(sK2))
    | k1_xboole_0 = u1_orders_2(sK2) ),
    inference(resolution,[],[f125,f165])).

fof(f165,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | k1_xboole_0 = u1_orders_2(sK2) ),
    inference(resolution,[],[f159,f95])).

fof(f471,plain,(
    ~ r2_hidden(sK3,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f469,f272])).

fof(f272,plain,(
    sP0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f237,f205])).

fof(f237,plain,(
    sP0(u1_orders_2(sK2),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f218,f148])).

fof(f218,plain,
    ( sP0(u1_orders_2(sK2),k1_xboole_0)
    | ~ sP1(u1_orders_2(sK2)) ),
    inference(backward_demodulation,[],[f109,f207])).

fof(f469,plain,
    ( ~ sP0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK3,k1_xboole_0) ),
    inference(resolution,[],[f264,f423])).

fof(f423,plain,(
    r2_hidden(sK4,k1_xboole_0) ),
    inference(resolution,[],[f402,f70])).

fof(f402,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0))
      | r2_hidden(sK4,k1_xboole_0) ) ),
    inference(resolution,[],[f395,f236])).

fof(f236,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f217,f207])).

fof(f217,plain,
    ( v1_xboole_0(k1_xboole_0)
    | r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f95,f207])).

fof(f264,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4,X0)
      | ~ sP0(k1_xboole_0,X0)
      | ~ r2_hidden(sK3,X0) ) ),
    inference(backward_demodulation,[],[f125,f205])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (461)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.49  % (460)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.49  % (466)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.49  % (458)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (481)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (468)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (485)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.50  % (461)Refutation not found, incomplete strategy% (461)------------------------------
% 0.20/0.50  % (461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (461)Memory used [KB]: 6140
% 0.20/0.50  % (461)Time elapsed: 0.094 s
% 0.20/0.50  % (461)------------------------------
% 0.20/0.50  % (461)------------------------------
% 0.20/0.50  % (458)Refutation not found, incomplete strategy% (458)------------------------------
% 0.20/0.50  % (458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (458)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (458)Memory used [KB]: 10746
% 0.20/0.50  % (458)Time elapsed: 0.072 s
% 0.20/0.50  % (458)------------------------------
% 0.20/0.50  % (458)------------------------------
% 0.20/0.51  % (464)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (487)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (493)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (464)Refutation not found, incomplete strategy% (464)------------------------------
% 0.20/0.51  % (464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (464)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (464)Memory used [KB]: 10618
% 0.20/0.51  % (464)Time elapsed: 0.069 s
% 0.20/0.51  % (464)------------------------------
% 0.20/0.51  % (464)------------------------------
% 0.20/0.51  % (462)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (490)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (459)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.51  % (494)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (462)Refutation not found, incomplete strategy% (462)------------------------------
% 0.20/0.51  % (462)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (462)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (462)Memory used [KB]: 6140
% 0.20/0.51  % (462)Time elapsed: 0.110 s
% 0.20/0.51  % (462)------------------------------
% 0.20/0.51  % (462)------------------------------
% 0.20/0.52  % (469)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.52  % (466)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f472,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(subsumption_resolution,[],[f471,f437])).
% 0.20/0.52  fof(f437,plain,(
% 0.20/0.52    r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f403,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(sK7(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0] : m1_subset_1(sK7(X0),k1_zfmisc_1(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(sK7(X0),k1_zfmisc_1(X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : ? [X1] : m1_subset_1(X1,k1_zfmisc_1(X0))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.20/0.52  fof(f403,plain,(
% 0.20/0.52    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK3,k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f395,f235])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0) | r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f212,f207])).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    k1_xboole_0 = u1_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f206,f131])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    r2_hidden(sK3,u1_struct_0(sK2)) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f86,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f48,f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    m1_subset_1(sK3,u1_struct_0(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ((sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f35,f34,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0)) => (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(sK2,X2,X1) & r1_orders_2(sK2,X1,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ? [X2] : (sK3 != X2 & r1_orders_2(sK2,X2,sK3) & r1_orders_2(sK2,sK3,X2) & m1_subset_1(X2,u1_struct_0(sK2))) => (sK3 != sK4 & r1_orders_2(sK2,sK4,sK3) & r1_orders_2(sK2,sK3,sK4) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (X1 != X2 & r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((X1 != X2 & (r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.20/0.52    inference(negated_conjecture,[],[f13])).
% 0.20/0.52  fof(f13,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)) => X1 = X2))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_orders_2)).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    ~r2_hidden(sK3,u1_struct_0(sK2)) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f202,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    sP0(u1_orders_2(sK2),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f148,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    ~sP1(u1_orders_2(sK2)) | sP0(u1_orders_2(sK2),u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f81,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP0(X0,X1) | ~r4_relat_2(X0,X1) | ~sP1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((r4_relat_2(X0,X1) | ~sP0(X0,X1)) & (sP0(X0,X1) | ~r4_relat_2(X0,X1))) | ~sP1(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> sP0(X0,X1)) | ~sP1(X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    r4_relat_2(u1_orders_2(sK2),u1_struct_0(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f78,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    v5_orders_2(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    r4_relat_2(u1_orders_2(sK2),u1_struct_0(sK2)) | ~v5_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f47,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0] : (((v5_orders_2(X0) | ~r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) & (r4_relat_2(u1_orders_2(X0),u1_struct_0(X0)) | ~v5_orders_2(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : ((v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => (v5_orders_2(X0) <=> r4_relat_2(u1_orders_2(X0),u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_orders_2)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    l1_orders_2(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    sP1(u1_orders_2(sK2))),
% 0.20/0.52    inference(resolution,[],[f147,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0] : (sP1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (sP1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(definition_folding,[],[f23,f31,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : (X2 = X3 | (~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r4_relat_2(X0,X1) <=> ! [X2,X3] : ((r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => X2 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_2)).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    v1_relat_1(u1_orders_2(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f145,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    v1_relat_1(u1_orders_2(sK2)) | ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))),
% 0.20/0.52    inference(resolution,[],[f80,f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))),
% 0.20/0.52    inference(resolution,[],[f47,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~sP0(u1_orders_2(sK2),u1_struct_0(sK2)) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f125,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    r2_hidden(sK4,u1_struct_0(sK2)) | k1_xboole_0 = u1_struct_0(sK2)),
% 0.20/0.52    inference(resolution,[],[f95,f68])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK2)) | r2_hidden(sK4,u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f49,f73])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4,X0) | ~r2_hidden(sK3,X0) | ~sP0(u1_orders_2(sK2),X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f124,f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f102,f47])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f101,f48])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f100,f49])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f50,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    r1_orders_2(sK2,sK3,sK4)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~r2_hidden(sK3,X0) | ~r2_hidden(sK4,X0) | ~sP0(u1_orders_2(sK2),X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f119,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    sK3 != sK4),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X0] : (sK3 = sK4 | ~r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK2)) | ~r2_hidden(sK3,X0) | ~r2_hidden(sK4,X0) | ~sP0(u1_orders_2(sK2),X0)) )),
% 0.20/0.52    inference(resolution,[],[f107,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~sP0(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f41,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => (sK5(X0,X1) != sK6(X0,X1) & r2_hidden(k4_tarski(sK6(X0,X1),sK5(X0,X1)),X0) & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0) & r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X4,X5] : (X4 = X5 | ~r2_hidden(k4_tarski(X5,X4),X0) | ~r2_hidden(k4_tarski(X4,X5),X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : (X2 != X3 & r2_hidden(k4_tarski(X3,X2),X0) & r2_hidden(k4_tarski(X2,X3),X0) & r2_hidden(X3,X1) & r2_hidden(X2,X1))) & (! [X2,X3] : (X2 = X3 | ~r2_hidden(k4_tarski(X3,X2),X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X2,X1)) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f30])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2))),
% 0.20/0.52    inference(subsumption_resolution,[],[f106,f47])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f105,f49])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f104,f48])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK4,sK3),u1_orders_2(sK2)) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f51,f56])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    r1_orders_2(sK2,sK4,sK3)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    r2_hidden(sK3,k1_xboole_0) | v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f86,f207])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    ( ! [X6,X5] : (~v1_xboole_0(X6) | ~m1_subset_1(X5,k1_zfmisc_1(X6))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f392,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.52  fof(f392,plain,(
% 0.20/0.52    ( ! [X6,X5] : (r2_hidden(k4_tarski(sK3,sK4),X5) | ~m1_subset_1(X5,k1_zfmisc_1(X6)) | ~v1_xboole_0(X6)) )),
% 0.20/0.52    inference(resolution,[],[f327,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.52  fof(f327,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | r2_hidden(k4_tarski(sK3,sK4),X0)) )),
% 0.20/0.52    inference(superposition,[],[f261,f68])).
% 0.20/0.52  fof(f261,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK3,sK4),k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f103,f205])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    k1_xboole_0 = u1_orders_2(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f204,f166])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    r2_hidden(sK3,u1_struct_0(sK2)) | k1_xboole_0 = u1_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f159,f86])).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    ~v1_xboole_0(u1_struct_0(sK2)) | k1_xboole_0 = u1_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f142,f68])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    v1_xboole_0(u1_orders_2(sK2)) | ~v1_xboole_0(u1_struct_0(sK2))),
% 0.20/0.52    inference(resolution,[],[f80,f72])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    ~r2_hidden(sK3,u1_struct_0(sK2)) | k1_xboole_0 = u1_orders_2(sK2)),
% 0.20/0.52    inference(subsumption_resolution,[],[f201,f150])).
% 0.20/0.52  fof(f201,plain,(
% 0.20/0.52    ~r2_hidden(sK3,u1_struct_0(sK2)) | ~sP0(u1_orders_2(sK2),u1_struct_0(sK2)) | k1_xboole_0 = u1_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f125,f165])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    r2_hidden(sK4,u1_struct_0(sK2)) | k1_xboole_0 = u1_orders_2(sK2)),
% 0.20/0.52    inference(resolution,[],[f159,f95])).
% 0.20/0.52  fof(f471,plain,(
% 0.20/0.52    ~r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f469,f272])).
% 0.20/0.52  fof(f272,plain,(
% 0.20/0.52    sP0(k1_xboole_0,k1_xboole_0)),
% 0.20/0.52    inference(backward_demodulation,[],[f237,f205])).
% 0.20/0.52  fof(f237,plain,(
% 0.20/0.52    sP0(u1_orders_2(sK2),k1_xboole_0)),
% 0.20/0.52    inference(subsumption_resolution,[],[f218,f148])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    sP0(u1_orders_2(sK2),k1_xboole_0) | ~sP1(u1_orders_2(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f109,f207])).
% 0.20/0.52  fof(f469,plain,(
% 0.20/0.52    ~sP0(k1_xboole_0,k1_xboole_0) | ~r2_hidden(sK3,k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f264,f423])).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    r2_hidden(sK4,k1_xboole_0)),
% 0.20/0.52    inference(resolution,[],[f402,f70])).
% 0.20/0.52  fof(f402,plain,(
% 0.20/0.52    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK4,k1_xboole_0)) )),
% 0.20/0.52    inference(resolution,[],[f395,f236])).
% 0.20/0.52  fof(f236,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0) | r2_hidden(sK4,k1_xboole_0)),
% 0.20/0.52    inference(forward_demodulation,[],[f217,f207])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0) | r2_hidden(sK4,u1_struct_0(sK2))),
% 0.20/0.52    inference(backward_demodulation,[],[f95,f207])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK4,X0) | ~sP0(k1_xboole_0,X0) | ~r2_hidden(sK3,X0)) )),
% 0.20/0.52    inference(backward_demodulation,[],[f125,f205])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (466)------------------------------
% 0.20/0.52  % (466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (466)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (466)Memory used [KB]: 1791
% 0.20/0.52  % (466)Time elapsed: 0.110 s
% 0.20/0.52  % (466)------------------------------
% 0.20/0.52  % (466)------------------------------
% 0.20/0.52  % (452)Success in time 0.164 s
%------------------------------------------------------------------------------
