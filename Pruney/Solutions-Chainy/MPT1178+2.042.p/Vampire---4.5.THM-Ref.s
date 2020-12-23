%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:31 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 266 expanded)
%              Number of leaves         :   32 (  97 expanded)
%              Depth                    :   14
%              Number of atoms          :  557 (1200 expanded)
%              Number of equality atoms :   59 ( 174 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f520,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f165,f296,f298,f300,f302,f304,f317,f376,f415,f418,f448,f487,f519])).

fof(f519,plain,
    ( ~ spl9_3
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(avatar_contradiction_clause,[],[f517])).

fof(f517,plain,
    ( $false
    | ~ spl9_3
    | ~ spl9_20
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(resolution,[],[f492,f366])).

fof(f366,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f364])).

fof(f364,plain,
    ( spl9_20
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f492,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_3
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(resolution,[],[f489,f137])).

fof(f137,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f135,f70])).

fof(f70,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f135,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f89,f133])).

fof(f133,plain,(
    k1_xboole_0 = sK7(k1_xboole_0) ),
    inference(resolution,[],[f127,f70])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK6(sK7(X0)),X0)
      | k1_xboole_0 = sK7(X0) ) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f89,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,sK7(X0))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK7(X0))
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
        | ~ r2_hidden(X2,sK7(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
          & ( ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK7(X0))
            | r1_xboole_0(X2,X0)
            | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
          & ( ( ~ r1_xboole_0(X2,X0)
              & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
            | ~ r2_hidden(X2,sK7(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | r1_xboole_0(X2,X0)
        | ~ r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
      & ( ( ~ r1_xboole_0(X2,X0)
          & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( ~ r1_xboole_0(X2,X0)
        & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e5_6__mcart_1)).

fof(f489,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0)
        | ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl9_3
    | ~ spl9_24
    | ~ spl9_28 ),
    inference(resolution,[],[f488,f450])).

fof(f450,plain,
    ( ! [X0] :
        ( m2_orders_2(X0,sK1,sK2)
        | ~ r2_hidden(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl9_3
    | ~ spl9_24 ),
    inference(forward_demodulation,[],[f449,f160])).

fof(f160,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k4_orders_2(sK1,sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl9_3
  <=> k1_zfmisc_1(k1_xboole_0) = k4_orders_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f449,plain,
    ( ! [X0] :
        ( m2_orders_2(X0,sK1,sK2)
        | ~ r2_hidden(X0,k4_orders_2(sK1,sK2)) )
    | ~ spl9_24 ),
    inference(resolution,[],[f447,f116])).

fof(f116,plain,(
    m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) ),
    inference(backward_demodulation,[],[f101,f69])).

fof(f69,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f101,plain,(
    m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0))) ),
    inference(definition_unfolding,[],[f66,f74])).

fof(f74,plain,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_orders_1)).

fof(f66,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK1,sK2))
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK1,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( k1_xboole_0 = k3_tarski(k4_orders_2(sK1,X1))
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1))) )
   => ( k1_xboole_0 = k3_tarski(k4_orders_2(sK1,sK2))
      & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f447,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
        | m2_orders_2(X0,sK1,X1)
        | ~ r2_hidden(X0,k4_orders_2(sK1,X1)) )
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl9_24
  <=> ! [X1,X0] :
        ( m2_orders_2(X0,sK1,X1)
        | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
        | ~ r2_hidden(X0,k4_orders_2(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f488,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK1,sK2)
        | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) )
    | ~ spl9_28 ),
    inference(resolution,[],[f486,f116])).

fof(f486,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
        | r2_hidden(k1_funct_1(X0,u1_struct_0(sK1)),X1)
        | ~ m2_orders_2(X1,sK1,X0) )
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl9_28
  <=> ! [X1,X0] :
        ( r2_hidden(k1_funct_1(X0,u1_struct_0(sK1)),X1)
        | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
        | ~ m2_orders_2(X1,sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f487,plain,
    ( spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | spl9_28 ),
    inference(avatar_split_clause,[],[f483,f485,f279,f275,f271,f267])).

fof(f267,plain,
    ( spl9_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f271,plain,
    ( spl9_11
  <=> v3_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f275,plain,
    ( spl9_12
  <=> v4_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f279,plain,
    ( spl9_13
  <=> v5_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f483,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X0,u1_struct_0(sK1)),X1)
      | ~ m2_orders_2(X1,sK1,X0)
      | ~ m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f117,f65])).

fof(f65,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_zfmisc_1(k1_xboole_0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f103,f69])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f82,f74])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(f448,plain,
    ( spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | spl9_24 ),
    inference(avatar_split_clause,[],[f444,f446,f279,f275,f271,f267])).

fof(f444,plain,(
    ! [X0,X1] :
      ( m2_orders_2(X0,sK1,X1)
      | ~ r2_hidden(X0,k4_orders_2(sK1,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
      | ~ v5_orders_2(sK1)
      | ~ v4_orders_2(sK1)
      | ~ v3_orders_2(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f121,f65])).

fof(f121,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_zfmisc_1(k1_xboole_0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f111,f69])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f83,f74])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK5(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK5(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK5(X0,X1,X2),X0,X1)
                    | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK5(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( m2_orders_2(sK5(X0,X1,X2),X0,X1)
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f418,plain,(
    spl9_23 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl9_23 ),
    inference(resolution,[],[f414,f68])).

fof(f68,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f414,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl9_23 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl9_23
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f415,plain,
    ( spl9_10
    | ~ spl9_11
    | ~ spl9_12
    | ~ spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_23
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f410,f162,f412,f287,f283,f279,f275,f271,f267])).

fof(f283,plain,
    ( spl9_14
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f287,plain,
    ( spl9_15
  <=> m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f162,plain,
    ( spl9_4
  <=> k1_xboole_0 = k4_orders_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f410,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ spl9_4 ),
    inference(superposition,[],[f122,f164])).

fof(f164,plain,
    ( k1_xboole_0 = k4_orders_2(sK1,sK2)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_zfmisc_1(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(forward_demodulation,[],[f109,f69])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_unfolding,[],[f93,f74])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f376,plain,(
    spl9_20 ),
    inference(avatar_contradiction_clause,[],[f374])).

fof(f374,plain,
    ( $false
    | spl9_20 ),
    inference(resolution,[],[f373,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f373,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl9_20 ),
    inference(resolution,[],[f365,f112])).

fof(f112,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK8(X0,X1),X0)
            | ~ r2_hidden(sK8(X0,X1),X1) )
          & ( r1_tarski(sK8(X0,X1),X0)
            | r2_hidden(sK8(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f56,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK8(X0,X1),X0)
          | ~ r2_hidden(sK8(X0,X1),X1) )
        & ( r1_tarski(sK8(X0,X1),X0)
          | r2_hidden(sK8(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f365,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl9_20 ),
    inference(avatar_component_clause,[],[f364])).

fof(f317,plain,(
    ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl9_10 ),
    inference(resolution,[],[f269,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f269,plain,
    ( v2_struct_0(sK1)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f267])).

fof(f304,plain,(
    spl9_15 ),
    inference(avatar_contradiction_clause,[],[f303])).

fof(f303,plain,
    ( $false
    | spl9_15 ),
    inference(resolution,[],[f289,f116])).

fof(f289,plain,
    ( ~ m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))
    | spl9_15 ),
    inference(avatar_component_clause,[],[f287])).

fof(f302,plain,(
    spl9_14 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | spl9_14 ),
    inference(resolution,[],[f285,f65])).

fof(f285,plain,
    ( ~ l1_orders_2(sK1)
    | spl9_14 ),
    inference(avatar_component_clause,[],[f283])).

fof(f300,plain,(
    spl9_13 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | spl9_13 ),
    inference(resolution,[],[f281,f64])).

fof(f64,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f281,plain,
    ( ~ v5_orders_2(sK1)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f279])).

fof(f298,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f297])).

fof(f297,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f277,f63])).

fof(f63,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f277,plain,
    ( ~ v4_orders_2(sK1)
    | spl9_12 ),
    inference(avatar_component_clause,[],[f275])).

fof(f296,plain,(
    spl9_11 ),
    inference(avatar_contradiction_clause,[],[f295])).

fof(f295,plain,
    ( $false
    | spl9_11 ),
    inference(resolution,[],[f273,f62])).

fof(f62,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f273,plain,
    ( ~ v3_orders_2(sK1)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f271])).

fof(f165,plain,
    ( spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f147,f162,f158])).

fof(f147,plain,
    ( k1_xboole_0 = k4_orders_2(sK1,sK2)
    | k1_zfmisc_1(k1_xboole_0) = k4_orders_2(sK1,sK2) ),
    inference(resolution,[],[f142,f123])).

fof(f123,plain,(
    r1_tarski(k4_orders_2(sK1,sK2),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f73,f67])).

fof(f67,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f142,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X0
      | k1_zfmisc_1(k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f98,f69])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:09:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (13985)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (13988)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (13987)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.52  % (13993)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.52  % (13994)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.24/0.52  % (13994)Refutation not found, incomplete strategy% (13994)------------------------------
% 1.24/0.52  % (13994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (13994)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.52  
% 1.24/0.52  % (13994)Memory used [KB]: 10618
% 1.24/0.52  % (13994)Time elapsed: 0.117 s
% 1.24/0.52  % (13994)------------------------------
% 1.24/0.52  % (13994)------------------------------
% 1.24/0.52  % (13989)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.52  % (13985)Refutation not found, incomplete strategy% (13985)------------------------------
% 1.24/0.52  % (13985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (14000)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.53  % (14002)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.24/0.53  % (13985)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (13985)Memory used [KB]: 10746
% 1.24/0.53  % (13985)Time elapsed: 0.115 s
% 1.24/0.53  % (13985)------------------------------
% 1.24/0.53  % (13985)------------------------------
% 1.24/0.53  % (13990)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.24/0.53  % (13996)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.53  % (13993)Refutation not found, incomplete strategy% (13993)------------------------------
% 1.24/0.53  % (13993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (13993)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (13993)Memory used [KB]: 10618
% 1.24/0.53  % (13993)Time elapsed: 0.119 s
% 1.24/0.53  % (13993)------------------------------
% 1.24/0.53  % (13993)------------------------------
% 1.24/0.53  % (13986)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.53  % (13991)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.24/0.53  % (13984)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.53  % (13987)Refutation not found, incomplete strategy% (13987)------------------------------
% 1.24/0.53  % (13987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (13987)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (13987)Memory used [KB]: 6268
% 1.24/0.53  % (13987)Time elapsed: 0.127 s
% 1.24/0.53  % (13987)------------------------------
% 1.24/0.53  % (13987)------------------------------
% 1.24/0.53  % (13983)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.24/0.54  % (14004)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.24/0.54  % (14008)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.24/0.54  % (14007)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.54  % (13998)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.54  % (14004)Refutation not found, incomplete strategy% (14004)------------------------------
% 1.35/0.54  % (14004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (14003)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.55  % (13999)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.35/0.55  % (14001)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (14014)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.55  % (14010)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.55  % (13997)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.55  % (14012)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.35/0.55  % (13999)Refutation not found, incomplete strategy% (13999)------------------------------
% 1.35/0.55  % (13999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (13999)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (13999)Memory used [KB]: 6268
% 1.35/0.55  % (13999)Time elapsed: 0.098 s
% 1.35/0.55  % (13999)------------------------------
% 1.35/0.55  % (13999)------------------------------
% 1.35/0.55  % (13996)Refutation found. Thanks to Tanya!
% 1.35/0.55  % SZS status Theorem for theBenchmark
% 1.35/0.55  % SZS output start Proof for theBenchmark
% 1.35/0.55  fof(f520,plain,(
% 1.35/0.55    $false),
% 1.35/0.55    inference(avatar_sat_refutation,[],[f165,f296,f298,f300,f302,f304,f317,f376,f415,f418,f448,f487,f519])).
% 1.35/0.55  fof(f519,plain,(
% 1.35/0.55    ~spl9_3 | ~spl9_20 | ~spl9_24 | ~spl9_28),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f517])).
% 1.35/0.55  fof(f517,plain,(
% 1.35/0.55    $false | (~spl9_3 | ~spl9_20 | ~spl9_24 | ~spl9_28)),
% 1.35/0.55    inference(resolution,[],[f492,f366])).
% 1.35/0.55  fof(f366,plain,(
% 1.35/0.55    r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl9_20),
% 1.35/0.55    inference(avatar_component_clause,[],[f364])).
% 1.35/0.55  fof(f364,plain,(
% 1.35/0.55    spl9_20 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 1.35/0.55  fof(f492,plain,(
% 1.35/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl9_3 | ~spl9_24 | ~spl9_28)),
% 1.35/0.55    inference(resolution,[],[f489,f137])).
% 1.35/0.55  fof(f137,plain,(
% 1.35/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.35/0.55    inference(resolution,[],[f135,f70])).
% 1.35/0.55  fof(f70,plain,(
% 1.35/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.35/0.55  fof(f135,plain,(
% 1.35/0.55    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.35/0.55    inference(superposition,[],[f89,f133])).
% 1.35/0.55  fof(f133,plain,(
% 1.35/0.55    k1_xboole_0 = sK7(k1_xboole_0)),
% 1.35/0.55    inference(resolution,[],[f127,f70])).
% 1.35/0.55  fof(f127,plain,(
% 1.35/0.55    ( ! [X0] : (~r1_xboole_0(sK6(sK7(X0)),X0) | k1_xboole_0 = sK7(X0)) )),
% 1.35/0.55    inference(resolution,[],[f89,f87])).
% 1.35/0.55  fof(f87,plain,(
% 1.35/0.55    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f50])).
% 1.35/0.55  fof(f50,plain,(
% 1.35/0.55    ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0)),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f31,f49])).
% 1.35/0.55  fof(f49,plain,(
% 1.35/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f31,plain,(
% 1.35/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.35/0.55    inference(ennf_transformation,[],[f2])).
% 1.35/0.55  fof(f2,axiom,(
% 1.35/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.35/0.55  fof(f89,plain,(
% 1.35/0.55    ( ! [X2,X0] : (~r2_hidden(X2,sK7(X0)) | ~r1_xboole_0(X2,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f54])).
% 1.35/0.55  fof(f54,plain,(
% 1.35/0.55    ! [X0] : ! [X2] : ((r2_hidden(X2,sK7(X0)) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,sK7(X0))))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f52,f53])).
% 1.35/0.55  fof(f53,plain,(
% 1.35/0.55    ! [X0] : (? [X1] : ! [X2] : ((r2_hidden(X2,X1) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,X1))) => ! [X2] : ((r2_hidden(X2,sK7(X0)) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,sK7(X0)))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f52,plain,(
% 1.35/0.55    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,X1)))),
% 1.35/0.55    inference(flattening,[],[f51])).
% 1.35/0.55  fof(f51,plain,(
% 1.35/0.55    ! [X0] : ? [X1] : ! [X2] : ((r2_hidden(X2,X1) | (r1_xboole_0(X2,X0) | ~r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0)))))))) & ((~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))) | ~r2_hidden(X2,X1)))),
% 1.35/0.55    inference(nnf_transformation,[],[f13])).
% 1.35/0.55  fof(f13,axiom,(
% 1.35/0.55    ! [X0] : ? [X1] : ! [X2] : (r2_hidden(X2,X1) <=> (~r1_xboole_0(X2,X0) & r2_hidden(X2,k3_tarski(k3_tarski(k3_tarski(k3_tarski(k3_tarski(X0))))))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e5_6__mcart_1)).
% 1.35/0.55  fof(f489,plain,(
% 1.35/0.55    ( ! [X0] : (r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0) | ~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl9_3 | ~spl9_24 | ~spl9_28)),
% 1.35/0.55    inference(resolution,[],[f488,f450])).
% 1.35/0.55  fof(f450,plain,(
% 1.35/0.55    ( ! [X0] : (m2_orders_2(X0,sK1,sK2) | ~r2_hidden(X0,k1_zfmisc_1(k1_xboole_0))) ) | (~spl9_3 | ~spl9_24)),
% 1.35/0.55    inference(forward_demodulation,[],[f449,f160])).
% 1.35/0.55  fof(f160,plain,(
% 1.35/0.55    k1_zfmisc_1(k1_xboole_0) = k4_orders_2(sK1,sK2) | ~spl9_3),
% 1.35/0.55    inference(avatar_component_clause,[],[f158])).
% 1.35/0.55  fof(f158,plain,(
% 1.35/0.55    spl9_3 <=> k1_zfmisc_1(k1_xboole_0) = k4_orders_2(sK1,sK2)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.35/0.55  fof(f449,plain,(
% 1.35/0.55    ( ! [X0] : (m2_orders_2(X0,sK1,sK2) | ~r2_hidden(X0,k4_orders_2(sK1,sK2))) ) | ~spl9_24),
% 1.35/0.55    inference(resolution,[],[f447,f116])).
% 1.35/0.55  fof(f116,plain,(
% 1.35/0.55    m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))),
% 1.35/0.55    inference(backward_demodulation,[],[f101,f69])).
% 1.35/0.55  fof(f69,plain,(
% 1.35/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.35/0.55    inference(cnf_transformation,[],[f11])).
% 1.35/0.55  fof(f11,axiom,(
% 1.35/0.55    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.35/0.55  fof(f101,plain,(
% 1.35/0.55    m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_tarski(k1_xboole_0)))),
% 1.35/0.55    inference(definition_unfolding,[],[f66,f74])).
% 1.35/0.55  fof(f74,plain,(
% 1.35/0.55    ( ! [X0] : (k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f16])).
% 1.35/0.55  fof(f16,axiom,(
% 1.35/0.55    ! [X0] : k1_orders_1(X0) = k7_subset_1(k1_zfmisc_1(X0),k9_setfam_1(X0),k1_tarski(k1_xboole_0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_orders_1)).
% 1.35/0.55  fof(f66,plain,(
% 1.35/0.55    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f38,plain,(
% 1.35/0.55    (k1_xboole_0 = k3_tarski(k4_orders_2(sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f23,f37,f36])).
% 1.35/0.55  fof(f36,plain,(
% 1.35/0.55    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f37,plain,(
% 1.35/0.55    ? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK1,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK1)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(sK1,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK1))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f23,plain,(
% 1.35/0.55    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.35/0.55    inference(flattening,[],[f22])).
% 1.35/0.55  fof(f22,plain,(
% 1.35/0.55    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f20])).
% 1.35/0.55  fof(f20,negated_conjecture,(
% 1.35/0.55    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.35/0.55    inference(negated_conjecture,[],[f19])).
% 1.35/0.55  fof(f19,conjecture,(
% 1.35/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 1.35/0.55  fof(f447,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | m2_orders_2(X0,sK1,X1) | ~r2_hidden(X0,k4_orders_2(sK1,X1))) ) | ~spl9_24),
% 1.35/0.55    inference(avatar_component_clause,[],[f446])).
% 1.35/0.55  fof(f446,plain,(
% 1.35/0.55    spl9_24 <=> ! [X1,X0] : (m2_orders_2(X0,sK1,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | ~r2_hidden(X0,k4_orders_2(sK1,X1)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.35/0.55  fof(f488,plain,(
% 1.35/0.55    ( ! [X0] : (~m2_orders_2(X0,sK1,sK2) | r2_hidden(k1_funct_1(sK2,u1_struct_0(sK1)),X0)) ) | ~spl9_28),
% 1.35/0.55    inference(resolution,[],[f486,f116])).
% 1.35/0.55  fof(f486,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK1)),X1) | ~m2_orders_2(X1,sK1,X0)) ) | ~spl9_28),
% 1.35/0.55    inference(avatar_component_clause,[],[f485])).
% 1.35/0.55  fof(f485,plain,(
% 1.35/0.55    spl9_28 <=> ! [X1,X0] : (r2_hidden(k1_funct_1(X0,u1_struct_0(sK1)),X1) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | ~m2_orders_2(X1,sK1,X0))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 1.35/0.55  fof(f487,plain,(
% 1.35/0.55    spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | spl9_28),
% 1.35/0.55    inference(avatar_split_clause,[],[f483,f485,f279,f275,f271,f267])).
% 1.35/0.55  fof(f267,plain,(
% 1.35/0.55    spl9_10 <=> v2_struct_0(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.35/0.55  fof(f271,plain,(
% 1.35/0.55    spl9_11 <=> v3_orders_2(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.35/0.55  fof(f275,plain,(
% 1.35/0.55    spl9_12 <=> v4_orders_2(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.35/0.55  fof(f279,plain,(
% 1.35/0.55    spl9_13 <=> v5_orders_2(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 1.35/0.55  fof(f483,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X0,u1_struct_0(sK1)),X1) | ~m2_orders_2(X1,sK1,X0) | ~m1_orders_1(X0,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | ~v5_orders_2(sK1) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) )),
% 1.35/0.55    inference(resolution,[],[f117,f65])).
% 1.35/0.55  fof(f65,plain,(
% 1.35/0.55    l1_orders_2(sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f117,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_zfmisc_1(k1_xboole_0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(forward_demodulation,[],[f103,f69])).
% 1.35/0.55  fof(f103,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f82,f74])).
% 1.35/0.55  fof(f82,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f28])).
% 1.35/0.55  fof(f28,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(flattening,[],[f27])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f18])).
% 1.35/0.55  fof(f18,axiom,(
% 1.35/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 1.35/0.55  fof(f448,plain,(
% 1.35/0.55    spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | spl9_24),
% 1.35/0.55    inference(avatar_split_clause,[],[f444,f446,f279,f275,f271,f267])).
% 1.35/0.55  fof(f444,plain,(
% 1.35/0.55    ( ! [X0,X1] : (m2_orders_2(X0,sK1,X1) | ~r2_hidden(X0,k4_orders_2(sK1,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | ~v5_orders_2(sK1) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) )),
% 1.35/0.55    inference(resolution,[],[f121,f65])).
% 1.35/0.55  fof(f121,plain,(
% 1.35/0.55    ( ! [X4,X0,X1] : (~l1_orders_2(X0) | m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_zfmisc_1(k1_xboole_0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(forward_demodulation,[],[f111,f69])).
% 1.35/0.55  fof(f111,plain,(
% 1.35/0.55    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(equality_resolution,[],[f107])).
% 1.35/0.55  fof(f107,plain,(
% 1.35/0.55    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f83,f74])).
% 1.35/0.55  fof(f83,plain,(
% 1.35/0.55    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f48])).
% 1.35/0.55  fof(f48,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK5(X0,X1,X2),X0,X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (m2_orders_2(sK5(X0,X1,X2),X0,X1) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f46,f47])).
% 1.35/0.55  fof(f47,plain,(
% 1.35/0.55    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK5(X0,X1,X2),X0,X1) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (m2_orders_2(sK5(X0,X1,X2),X0,X1) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f46,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(rectify,[],[f45])).
% 1.35/0.55  fof(f45,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(nnf_transformation,[],[f30])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(flattening,[],[f29])).
% 1.35/0.55  fof(f29,plain,(
% 1.35/0.55    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f15])).
% 1.35/0.55  fof(f15,axiom,(
% 1.35/0.55    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 1.35/0.55  fof(f418,plain,(
% 1.35/0.55    spl9_23),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f416])).
% 1.35/0.55  fof(f416,plain,(
% 1.35/0.55    $false | spl9_23),
% 1.35/0.55    inference(resolution,[],[f414,f68])).
% 1.35/0.55  fof(f68,plain,(
% 1.35/0.55    v1_xboole_0(k1_xboole_0)),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    v1_xboole_0(k1_xboole_0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.35/0.55  fof(f414,plain,(
% 1.35/0.55    ~v1_xboole_0(k1_xboole_0) | spl9_23),
% 1.35/0.55    inference(avatar_component_clause,[],[f412])).
% 1.35/0.55  fof(f412,plain,(
% 1.35/0.55    spl9_23 <=> v1_xboole_0(k1_xboole_0)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.35/0.55  fof(f415,plain,(
% 1.35/0.55    spl9_10 | ~spl9_11 | ~spl9_12 | ~spl9_13 | ~spl9_14 | ~spl9_15 | ~spl9_23 | ~spl9_4),
% 1.35/0.55    inference(avatar_split_clause,[],[f410,f162,f412,f287,f283,f279,f275,f271,f267])).
% 1.35/0.55  fof(f283,plain,(
% 1.35/0.55    spl9_14 <=> l1_orders_2(sK1)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.35/0.55  fof(f287,plain,(
% 1.35/0.55    spl9_15 <=> m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0)))),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.35/0.55  fof(f162,plain,(
% 1.35/0.55    spl9_4 <=> k1_xboole_0 = k4_orders_2(sK1,sK2)),
% 1.35/0.55    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.35/0.55  fof(f410,plain,(
% 1.35/0.55    ~v1_xboole_0(k1_xboole_0) | ~m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | ~l1_orders_2(sK1) | ~v5_orders_2(sK1) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1) | ~spl9_4),
% 1.35/0.55    inference(superposition,[],[f122,f164])).
% 1.35/0.55  fof(f164,plain,(
% 1.35/0.55    k1_xboole_0 = k4_orders_2(sK1,sK2) | ~spl9_4),
% 1.35/0.55    inference(avatar_component_clause,[],[f162])).
% 1.35/0.55  fof(f122,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_zfmisc_1(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(forward_demodulation,[],[f109,f69])).
% 1.35/0.55  fof(f109,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k7_subset_1(k1_zfmisc_1(u1_struct_0(X0)),k9_setfam_1(u1_struct_0(X0)),k1_tarski(k1_xboole_0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f93,f74])).
% 1.35/0.55  fof(f93,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f33])).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.35/0.55    inference(flattening,[],[f32])).
% 1.35/0.55  fof(f32,plain,(
% 1.35/0.55    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.35/0.55    inference(ennf_transformation,[],[f17])).
% 1.35/0.55  fof(f17,axiom,(
% 1.35/0.55    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 1.35/0.55  fof(f376,plain,(
% 1.35/0.55    spl9_20),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f374])).
% 1.35/0.55  fof(f374,plain,(
% 1.35/0.55    $false | spl9_20),
% 1.35/0.55    inference(resolution,[],[f373,f71])).
% 1.35/0.55  fof(f71,plain,(
% 1.35/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.35/0.55  fof(f373,plain,(
% 1.35/0.55    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl9_20),
% 1.35/0.55    inference(resolution,[],[f365,f112])).
% 1.35/0.55  fof(f112,plain,(
% 1.35/0.55    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.35/0.55    inference(equality_resolution,[],[f95])).
% 1.35/0.55  fof(f95,plain,(
% 1.35/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.35/0.55    inference(cnf_transformation,[],[f58])).
% 1.35/0.55  fof(f58,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r1_tarski(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f56,f57])).
% 1.35/0.55  fof(f57,plain,(
% 1.35/0.55    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK8(X0,X1),X0) | ~r2_hidden(sK8(X0,X1),X1)) & (r1_tarski(sK8(X0,X1),X0) | r2_hidden(sK8(X0,X1),X1))))),
% 1.35/0.55    introduced(choice_axiom,[])).
% 1.35/0.55  fof(f56,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(rectify,[],[f55])).
% 1.35/0.55  fof(f55,plain,(
% 1.35/0.55    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.35/0.55    inference(nnf_transformation,[],[f7])).
% 1.35/0.55  fof(f7,axiom,(
% 1.35/0.55    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.35/0.55  fof(f365,plain,(
% 1.35/0.55    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl9_20),
% 1.35/0.55    inference(avatar_component_clause,[],[f364])).
% 1.35/0.55  fof(f317,plain,(
% 1.35/0.55    ~spl9_10),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f316])).
% 1.35/0.55  fof(f316,plain,(
% 1.35/0.55    $false | ~spl9_10),
% 1.35/0.55    inference(resolution,[],[f269,f61])).
% 1.35/0.55  fof(f61,plain,(
% 1.35/0.55    ~v2_struct_0(sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f269,plain,(
% 1.35/0.55    v2_struct_0(sK1) | ~spl9_10),
% 1.35/0.55    inference(avatar_component_clause,[],[f267])).
% 1.35/0.55  fof(f304,plain,(
% 1.35/0.55    spl9_15),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f303])).
% 1.35/0.55  fof(f303,plain,(
% 1.35/0.55    $false | spl9_15),
% 1.35/0.55    inference(resolution,[],[f289,f116])).
% 1.35/0.55  fof(f289,plain,(
% 1.35/0.55    ~m1_orders_1(sK2,k7_subset_1(k1_zfmisc_1(u1_struct_0(sK1)),k9_setfam_1(u1_struct_0(sK1)),k1_zfmisc_1(k1_xboole_0))) | spl9_15),
% 1.35/0.55    inference(avatar_component_clause,[],[f287])).
% 1.35/0.55  fof(f302,plain,(
% 1.35/0.55    spl9_14),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f301])).
% 1.35/0.55  fof(f301,plain,(
% 1.35/0.55    $false | spl9_14),
% 1.35/0.55    inference(resolution,[],[f285,f65])).
% 1.35/0.55  fof(f285,plain,(
% 1.35/0.55    ~l1_orders_2(sK1) | spl9_14),
% 1.35/0.55    inference(avatar_component_clause,[],[f283])).
% 1.35/0.55  fof(f300,plain,(
% 1.35/0.55    spl9_13),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f299])).
% 1.35/0.55  fof(f299,plain,(
% 1.35/0.55    $false | spl9_13),
% 1.35/0.55    inference(resolution,[],[f281,f64])).
% 1.35/0.55  fof(f64,plain,(
% 1.35/0.55    v5_orders_2(sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f281,plain,(
% 1.35/0.55    ~v5_orders_2(sK1) | spl9_13),
% 1.35/0.55    inference(avatar_component_clause,[],[f279])).
% 1.35/0.55  fof(f298,plain,(
% 1.35/0.55    spl9_12),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f297])).
% 1.35/0.55  fof(f297,plain,(
% 1.35/0.55    $false | spl9_12),
% 1.35/0.55    inference(resolution,[],[f277,f63])).
% 1.35/0.55  fof(f63,plain,(
% 1.35/0.55    v4_orders_2(sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f277,plain,(
% 1.35/0.55    ~v4_orders_2(sK1) | spl9_12),
% 1.35/0.55    inference(avatar_component_clause,[],[f275])).
% 1.35/0.55  fof(f296,plain,(
% 1.35/0.55    spl9_11),
% 1.35/0.55    inference(avatar_contradiction_clause,[],[f295])).
% 1.35/0.55  fof(f295,plain,(
% 1.35/0.55    $false | spl9_11),
% 1.35/0.55    inference(resolution,[],[f273,f62])).
% 1.35/0.55  fof(f62,plain,(
% 1.35/0.55    v3_orders_2(sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f273,plain,(
% 1.35/0.55    ~v3_orders_2(sK1) | spl9_11),
% 1.35/0.55    inference(avatar_component_clause,[],[f271])).
% 1.35/0.55  fof(f165,plain,(
% 1.35/0.55    spl9_3 | spl9_4),
% 1.35/0.55    inference(avatar_split_clause,[],[f147,f162,f158])).
% 1.35/0.55  fof(f147,plain,(
% 1.35/0.55    k1_xboole_0 = k4_orders_2(sK1,sK2) | k1_zfmisc_1(k1_xboole_0) = k4_orders_2(sK1,sK2)),
% 1.35/0.55    inference(resolution,[],[f142,f123])).
% 1.35/0.55  fof(f123,plain,(
% 1.35/0.55    r1_tarski(k4_orders_2(sK1,sK2),k1_zfmisc_1(k1_xboole_0))),
% 1.35/0.55    inference(superposition,[],[f73,f67])).
% 1.35/0.55  fof(f67,plain,(
% 1.35/0.55    k1_xboole_0 = k3_tarski(k4_orders_2(sK1,sK2))),
% 1.35/0.55    inference(cnf_transformation,[],[f38])).
% 1.35/0.55  fof(f73,plain,(
% 1.35/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f10])).
% 1.35/0.55  fof(f10,axiom,(
% 1.35/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 1.35/0.55  fof(f142,plain,(
% 1.35/0.55    ( ! [X0] : (~r1_tarski(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0 | k1_zfmisc_1(k1_xboole_0) = X0) )),
% 1.35/0.55    inference(superposition,[],[f98,f69])).
% 1.35/0.55  fof(f98,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f60])).
% 1.35/0.55  fof(f60,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.35/0.55    inference(flattening,[],[f59])).
% 1.35/0.55  fof(f59,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.35/0.55    inference(nnf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.35/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (13996)------------------------------
% 1.35/0.55  % (13996)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (13996)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (13996)Memory used [KB]: 6396
% 1.35/0.55  % (13996)Time elapsed: 0.130 s
% 1.35/0.55  % (13996)------------------------------
% 1.35/0.55  % (13996)------------------------------
% 1.35/0.55  % (13979)Success in time 0.185 s
%------------------------------------------------------------------------------
