%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 838 expanded)
%              Number of leaves         :   20 ( 222 expanded)
%              Depth                    :   28
%              Number of atoms          :  493 (4130 expanded)
%              Number of equality atoms :   57 ( 627 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f468,plain,(
    $false ),
    inference(subsumption_resolution,[],[f465,f60])).

fof(f60,plain,(
    k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6))
    & l1_orders_2(sK6)
    & v5_orders_2(sK6)
    & v4_orders_2(sK6)
    & v3_orders_2(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6))
      & l1_orders_2(sK6)
      & v5_orders_2(sK6)
      & v4_orders_2(sK6)
      & v3_orders_2(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).

fof(f465,plain,(
    k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f451,f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( sP2(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP2(sK7(X0),X0)
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP2(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f22,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

% (26055)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f451,plain,(
    ~ r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_orders_2(sK6,k2_struct_0(sK6))) ),
    inference(subsumption_resolution,[],[f447,f158])).

fof(f158,plain,(
    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6))) ),
    inference(forward_demodulation,[],[f126,f127])).

fof(f127,plain,(
    k2_struct_0(sK6) = u1_struct_0(sK6) ),
    inference(resolution,[],[f116,f61])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f116,plain,(
    l1_struct_0(sK6) ),
    inference(resolution,[],[f59,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f59,plain,(
    l1_orders_2(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6))) ),
    inference(resolution,[],[f116,f62])).

fof(f62,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f447,plain,
    ( ~ r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_orders_2(sK6,k2_struct_0(sK6)))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6))) ),
    inference(resolution,[],[f445,f180])).

fof(f180,plain,(
    ! [X0,X1] :
      ( sP4(X0,sK6,X1)
      | ~ r2_hidden(X1,k2_orders_2(sK6,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(subsumption_resolution,[],[f178,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK6,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(forward_demodulation,[],[f120,f127])).

fof(f120,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK6,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(subsumption_resolution,[],[f119,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f119,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK6,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f118,f56])).

fof(f56,plain,(
    v3_orders_2(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f118,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK6,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f117,f57])).

fof(f57,plain,(
    v4_orders_2(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK6,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f113,f58])).

fof(f58,plain,(
    v5_orders_2(sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f113,plain,(
    ! [X0,X1] :
      ( sP5(X0,sK6,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f59,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP5(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f26,f34,f33,f32])).

fof(f32,plain,(
    ! [X3,X1,X2] :
      ( sP3(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X3,X4)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( sP4(X2,X1,X0)
    <=> ? [X3] :
          ( sP3(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

% (26035)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP4(X2,X1,X0) )
      | ~ sP5(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK6,X0))
      | sP4(X0,sK6,X1)
      | ~ sP5(X1,sK6,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(superposition,[],[f77,f175])).

fof(f175,plain,(
    ! [X2] :
      ( k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(forward_demodulation,[],[f124,f127])).

fof(f124,plain,(
    ! [X2] :
      ( k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) ) ),
    inference(subsumption_resolution,[],[f123,f55])).

fof(f123,plain,(
    ! [X2] :
      ( k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f122,f56])).

fof(f122,plain,(
    ! [X2] :
      ( k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f121,f57])).

fof(f121,plain,(
    ! [X2] :
      ( k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(subsumption_resolution,[],[f114,f58])).

fof(f114,plain,(
    ! [X2] :
      ( k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))
      | ~ v5_orders_2(sK6)
      | ~ v4_orders_2(sK6)
      | ~ v3_orders_2(sK6)
      | v2_struct_0(sK6) ) ),
    inference(resolution,[],[f59,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f445,plain,(
    ~ sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) ),
    inference(subsumption_resolution,[],[f439,f158])).

fof(f439,plain,
    ( ~ sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))
    | ~ m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6))) ),
    inference(resolution,[],[f430,f254])).

fof(f254,plain,(
    ! [X4,X5] :
      ( sP3(X5,sK6,X4)
      | ~ sP4(X4,sK6,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(subsumption_resolution,[],[f251,f163])).

fof(f163,plain,(
    ! [X2,X3] :
      ( ~ sP4(X2,sK6,X3)
      | r2_hidden(X3,a_2_1_orders_2(sK6,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(resolution,[],[f157,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f251,plain,(
    ! [X4,X5] :
      ( sP3(X5,sK6,X4)
      | ~ sP4(X4,sK6,X5)
      | ~ r2_hidden(X5,a_2_1_orders_2(sK6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(superposition,[],[f81,f189])).

fof(f189,plain,(
    ! [X4,X5] :
      ( sK8(X4,sK6,X5) = X5
      | ~ r2_hidden(X5,a_2_1_orders_2(sK6,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(resolution,[],[f162,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = X2
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ sP3(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP3(sK8(X0,X1,X2),X1,X0)
          & sK8(X0,X1,X2) = X2
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP3(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP3(sK8(X0,X1,X2),X1,X0)
        & sK8(X0,X1,X2) = X2
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ! [X3] :
            ( ~ sP3(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP3(X4,X1,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ( sP4(X2,X1,X0)
        | ! [X3] :
            ( ~ sP3(X3,X1,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP3(X3,X1,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP4(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f162,plain,(
    ! [X0,X1] :
      ( sP4(X0,sK6,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ r2_hidden(X1,a_2_1_orders_2(sK6,X0)) ) ),
    inference(resolution,[],[f157,f77])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK8(X0,X1,X2),X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f430,plain,(
    ~ sP3(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f427,f382])).

fof(f382,plain,(
    m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f381,f60])).

fof(f381,plain,
    ( m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6))
    | k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6)) ),
    inference(resolution,[],[f277,f158])).

fof(f277,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))
      | m1_subset_1(sK7(k2_orders_2(sK6,X0)),k2_struct_0(sK6))
      | k1_xboole_0 = k2_orders_2(sK6,X0) ) ),
    inference(resolution,[],[f260,f74])).

fof(f260,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_orders_2(sK6,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6)))
      | m1_subset_1(X0,k2_struct_0(sK6)) ) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k2_struct_0(sK6))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6)))
      | ~ r2_hidden(X0,k2_orders_2(sK6,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(resolution,[],[f253,f180])).

fof(f253,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0,sK6,X1)
      | m1_subset_1(X1,k2_struct_0(sK6))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(forward_demodulation,[],[f252,f127])).

fof(f252,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(sK6))
      | ~ sP4(X0,sK6,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(subsumption_resolution,[],[f250,f163])).

fof(f250,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(sK6))
      | ~ sP4(X0,sK6,X1)
      | ~ r2_hidden(X1,a_2_1_orders_2(sK6,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) ) ),
    inference(superposition,[],[f79,f189])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f427,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK6))
      | ~ sP3(X6,sK6,k2_struct_0(sK6)) ) ),
    inference(duplicate_literal_removal,[],[f426])).

fof(f426,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k2_struct_0(sK6))
      | ~ m1_subset_1(X6,k2_struct_0(sK6))
      | ~ sP3(X6,sK6,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f371,f88])).

fof(f88,plain,(
    ! [X2,X1] : ~ sP0(X1,X1,X2) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 != X1
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | X0 = X1
        | ~ r1_orders_2(X2,X1,X0) )
      & ( ( X0 != X1
          & r1_orders_2(X2,X1,X0) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( sP0(X2,X1,X0)
        | X1 = X2
        | ~ r1_orders_2(X0,X1,X2) )
      & ( ( X1 != X2
          & r1_orders_2(X0,X1,X2) )
        | ~ sP0(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( X1 != X2
        & r1_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f371,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0,sK6)
      | ~ m1_subset_1(X1,k2_struct_0(sK6))
      | ~ m1_subset_1(X0,k2_struct_0(sK6))
      | ~ sP3(X0,sK6,k2_struct_0(sK6)) ) ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,sK6,k2_struct_0(sK6))
      | ~ m1_subset_1(X1,k2_struct_0(sK6))
      | ~ m1_subset_1(X0,k2_struct_0(sK6))
      | sP0(X1,X0,sK6)
      | ~ m1_subset_1(X1,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f367,f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( ~ r2_orders_2(sK6,X1,X0)
      | ~ m1_subset_1(X1,k2_struct_0(sK6))
      | sP0(X0,X1,sK6)
      | ~ m1_subset_1(X0,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f174,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_orders_2(X0,X1,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_orders_2(X0,X1,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_orders_2(X0,X1,X2)
      <=> sP0(X2,X1,X0) )
      | ~ sP1(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f174,plain,(
    ! [X4,X3] :
      ( sP1(sK6,X3,X4)
      | ~ m1_subset_1(X4,k2_struct_0(sK6))
      | ~ m1_subset_1(X3,k2_struct_0(sK6)) ) ),
    inference(forward_demodulation,[],[f173,f127])).

fof(f173,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k2_struct_0(sK6))
      | sP1(sK6,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(sK6)) ) ),
    inference(forward_demodulation,[],[f115,f127])).

fof(f115,plain,(
    ! [X4,X3] :
      ( sP1(sK6,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK6))
      | ~ m1_subset_1(X3,u1_struct_0(sK6)) ) ),
    inference(resolution,[],[f59,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f17,f28,f27])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

fof(f367,plain,(
    ! [X4,X3] :
      ( r2_orders_2(sK6,X4,X3)
      | ~ sP3(X4,sK6,k2_struct_0(sK6))
      | ~ m1_subset_1(X3,k2_struct_0(sK6)) ) ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k2_struct_0(sK6))
      | ~ sP3(X4,sK6,k2_struct_0(sK6))
      | r2_orders_2(sK6,X4,X3)
      | ~ m1_subset_1(X3,k2_struct_0(sK6)) ) ),
    inference(resolution,[],[f220,f131])).

fof(f131,plain,(
    ~ v1_xboole_0(k2_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f130,f116])).

fof(f130,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK6))
    | ~ l1_struct_0(sK6) ),
    inference(superposition,[],[f128,f61])).

fof(f128,plain,(
    ~ v1_xboole_0(u1_struct_0(sK6)) ),
    inference(subsumption_resolution,[],[f125,f55])).

fof(f125,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK6))
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f116,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f220,plain,(
    ! [X4,X2,X3] :
      ( v1_xboole_0(X4)
      | ~ m1_subset_1(X3,k2_struct_0(sK6))
      | ~ sP3(X2,sK6,X4)
      | r2_orders_2(sK6,X2,X3)
      | ~ m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f140,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f140,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,X9)
      | r2_orders_2(sK6,X8,X7)
      | ~ m1_subset_1(X7,k2_struct_0(sK6))
      | ~ sP3(X8,sK6,X9) ) ),
    inference(superposition,[],[f83,f127])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_orders_2(X1,X0,X4)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r2_orders_2(X1,X0,sK9(X0,X1,X2))
          & r2_hidden(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X0,sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

% (26034)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X3,X1,X2] :
      ( ( sP3(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X3,X4)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X3,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:17:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (26041)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.49  % (26041)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (26057)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.49  % (26038)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (26037)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f465,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6))),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6)) & l1_orders_2(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f13,f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK6,k2_struct_0(sK6)) & l1_orders_2(sK6) & v5_orders_2(sK6) & v4_orders_2(sK6) & v3_orders_2(sK6) & ~v2_struct_0(sK6))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.50  fof(f465,plain,(
% 0.21/0.50    k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6))),
% 0.21/0.50    inference(resolution,[],[f451,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X0] : ((sP2(sK7(X0),X0) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f31,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) => (sP2(sK7(X0),X0) & r2_hidden(sK7(X0),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (sP2(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(definition_folding,[],[f22,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP2(X1,X0))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f2])).
% 0.21/0.50  % (26055)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.50  fof(f451,plain,(
% 0.21/0.50    ~r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_orders_2(sK6,k2_struct_0(sK6)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f447,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6)))),
% 0.21/0.50    inference(forward_demodulation,[],[f126,f127])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    k2_struct_0(sK6) = u1_struct_0(sK6)),
% 0.21/0.50    inference(resolution,[],[f116,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    l1_struct_0(sK6)),
% 0.21/0.50    inference(resolution,[],[f59,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    l1_orders_2(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(u1_struct_0(sK6)))),
% 0.21/0.50    inference(resolution,[],[f116,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    ~r2_hidden(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_orders_2(sK6,k2_struct_0(sK6))) | ~m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6)))),
% 0.21/0.50    inference(resolution,[],[f445,f180])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP4(X0,sK6,X1) | ~r2_hidden(X1,k2_orders_2(sK6,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f178,f157])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP5(X0,sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f120,f127])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP5(X0,sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f119,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~v2_struct_0(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP5(X0,sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f118,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    v3_orders_2(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP5(X0,sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    v4_orders_2(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP5(X0,sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f113,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    v5_orders_2(sK6)),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP5(X0,sK6,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK6))) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(resolution,[],[f59,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (sP5(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.50    inference(definition_folding,[],[f26,f34,f33,f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X3,X1,X2] : (sP3(X3,X1,X2) <=> ! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (sP4(X2,X1,X0) <=> ? [X3] : (sP3(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.50  % (26035)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP4(X2,X1,X0)) | ~sP5(X0,X1,X2))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(sK6,X0)) | sP4(X0,sK6,X1) | ~sP5(X1,sK6,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(superposition,[],[f77,f175])).
% 0.21/0.50  fof(f175,plain,(
% 0.21/0.50    ( ! [X2] : (k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f124,f127])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    ( ! [X2] : (k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f55])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X2] : (k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f56])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X2] : (k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f121,f57])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X2] : (k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f114,f58])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ( ! [X2] : (k2_orders_2(sK6,X2) = a_2_1_orders_2(sK6,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK6))) | ~v5_orders_2(sK6) | ~v4_orders_2(sK6) | ~v3_orders_2(sK6) | v2_struct_0(sK6)) )),
% 0.21/0.50    inference(resolution,[],[f59,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP4(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP5(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP5(X0,X1,X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f34])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    ~sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6))))),
% 0.21/0.50    inference(subsumption_resolution,[],[f439,f158])).
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    ~sP4(k2_struct_0(sK6),sK6,sK7(k2_orders_2(sK6,k2_struct_0(sK6)))) | ~m1_subset_1(k2_struct_0(sK6),k1_zfmisc_1(k2_struct_0(sK6)))),
% 0.21/0.50    inference(resolution,[],[f430,f254])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X4,X5] : (sP3(X5,sK6,X4) | ~sP4(X4,sK6,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f251,f163])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X2,X3] : (~sP4(X2,sK6,X3) | r2_hidden(X3,a_2_1_orders_2(sK6,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(resolution,[],[f157,f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f251,plain,(
% 0.21/0.50    ( ! [X4,X5] : (sP3(X5,sK6,X4) | ~sP4(X4,sK6,X5) | ~r2_hidden(X5,a_2_1_orders_2(sK6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(superposition,[],[f81,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X4,X5] : (sK8(X4,sK6,X5) = X5 | ~r2_hidden(X5,a_2_1_orders_2(sK6,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(resolution,[],[f162,f80])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sK8(X0,X1,X2) = X2 | ~sP4(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~sP3(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((sP3(sK8(X0,X1,X2),X1,X0) & sK8(X0,X1,X2) = X2 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f48,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X4] : (sP3(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (sP3(sK8(X0,X1,X2),X1,X0) & sK8(X0,X1,X2) = X2 & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ! [X3] : (~sP3(X3,X1,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (sP3(X4,X1,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X2,X1,X0] : ((sP4(X2,X1,X0) | ! [X3] : (~sP3(X3,X1,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (sP3(X3,X1,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP4(X2,X1,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP4(X0,sK6,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | ~r2_hidden(X1,a_2_1_orders_2(sK6,X0))) )),
% 0.21/0.50    inference(resolution,[],[f157,f77])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP3(sK8(X0,X1,X2),X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f430,plain,(
% 0.21/0.50    ~sP3(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),sK6,k2_struct_0(sK6))),
% 0.21/0.50    inference(resolution,[],[f427,f382])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6))),
% 0.21/0.50    inference(subsumption_resolution,[],[f381,f60])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    m1_subset_1(sK7(k2_orders_2(sK6,k2_struct_0(sK6))),k2_struct_0(sK6)) | k1_xboole_0 = k2_orders_2(sK6,k2_struct_0(sK6))),
% 0.21/0.50    inference(resolution,[],[f277,f158])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6))) | m1_subset_1(sK7(k2_orders_2(sK6,X0)),k2_struct_0(sK6)) | k1_xboole_0 = k2_orders_2(sK6,X0)) )),
% 0.21/0.50    inference(resolution,[],[f260,f74])).
% 0.21/0.50  fof(f260,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_orders_2(sK6,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6))) | m1_subset_1(X0,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f255])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k2_struct_0(sK6)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6))) | ~r2_hidden(X0,k2_orders_2(sK6,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(resolution,[],[f253,f180])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP4(X0,sK6,X1) | m1_subset_1(X1,k2_struct_0(sK6)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f252,f127])).
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(sK6)) | ~sP4(X0,sK6,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f250,f163])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    ( ! [X0,X1] : (m1_subset_1(X1,u1_struct_0(sK6)) | ~sP4(X0,sK6,X1) | ~r2_hidden(X1,a_2_1_orders_2(sK6,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK6)))) )),
% 0.21/0.50    inference(superposition,[],[f79,f189])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) | ~sP4(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f50])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    ( ! [X6] : (~m1_subset_1(X6,k2_struct_0(sK6)) | ~sP3(X6,sK6,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f426])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    ( ! [X6] : (~m1_subset_1(X6,k2_struct_0(sK6)) | ~m1_subset_1(X6,k2_struct_0(sK6)) | ~sP3(X6,sK6,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(resolution,[],[f371,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X2,X1] : (~sP0(X1,X1,X2)) )),
% 0.21/0.50    inference(equality_resolution,[],[f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X0 != X1 | ~sP0(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | X0 = X1 | ~r1_orders_2(X2,X1,X0)) & ((X0 != X1 & r1_orders_2(X2,X1,X0)) | ~sP0(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 0.21/0.50    inference(flattening,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X2,X1,X0] : ((sP0(X2,X1,X0) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~sP0(X2,X1,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (X1 != X2 & r1_orders_2(X0,X1,X2)))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    ( ! [X0,X1] : (sP0(X1,X0,sK6) | ~m1_subset_1(X1,k2_struct_0(sK6)) | ~m1_subset_1(X0,k2_struct_0(sK6)) | ~sP3(X0,sK6,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f368])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~sP3(X0,sK6,k2_struct_0(sK6)) | ~m1_subset_1(X1,k2_struct_0(sK6)) | ~m1_subset_1(X0,k2_struct_0(sK6)) | sP0(X1,X0,sK6) | ~m1_subset_1(X1,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(resolution,[],[f367,f176])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_orders_2(sK6,X1,X0) | ~m1_subset_1(X1,k2_struct_0(sK6)) | sP0(X0,X1,sK6) | ~m1_subset_1(X0,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(resolution,[],[f174,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~r2_orders_2(X0,X1,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_orders_2(X0,X1,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_orders_2(X0,X1,X2))) | ~sP1(X0,X1,X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_orders_2(X0,X1,X2) <=> sP0(X2,X1,X0)) | ~sP1(X0,X1,X2))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ( ! [X4,X3] : (sP1(sK6,X3,X4) | ~m1_subset_1(X4,k2_struct_0(sK6)) | ~m1_subset_1(X3,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f173,f127])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~m1_subset_1(X4,k2_struct_0(sK6)) | sP1(sK6,X3,X4) | ~m1_subset_1(X3,u1_struct_0(sK6))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f115,f127])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    ( ! [X4,X3] : (sP1(sK6,X3,X4) | ~m1_subset_1(X4,u1_struct_0(sK6)) | ~m1_subset_1(X3,u1_struct_0(sK6))) )),
% 0.21/0.50    inference(resolution,[],[f59,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(definition_folding,[],[f17,f28,f27])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.50  fof(f367,plain,(
% 0.21/0.50    ( ! [X4,X3] : (r2_orders_2(sK6,X4,X3) | ~sP3(X4,sK6,k2_struct_0(sK6)) | ~m1_subset_1(X3,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f366])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    ( ! [X4,X3] : (~m1_subset_1(X3,k2_struct_0(sK6)) | ~sP3(X4,sK6,k2_struct_0(sK6)) | r2_orders_2(sK6,X4,X3) | ~m1_subset_1(X3,k2_struct_0(sK6))) )),
% 0.21/0.50    inference(resolution,[],[f220,f131])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK6))),
% 0.21/0.51    inference(subsumption_resolution,[],[f130,f116])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK6)) | ~l1_struct_0(sK6)),
% 0.21/0.51    inference(superposition,[],[f128,f61])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK6))),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f55])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~v1_xboole_0(u1_struct_0(sK6)) | v2_struct_0(sK6)),
% 0.21/0.51    inference(resolution,[],[f116,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (v1_xboole_0(X4) | ~m1_subset_1(X3,k2_struct_0(sK6)) | ~sP3(X2,sK6,X4) | r2_orders_2(sK6,X2,X3) | ~m1_subset_1(X3,X4)) )),
% 0.21/0.51    inference(resolution,[],[f140,f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ( ! [X8,X7,X9] : (~r2_hidden(X7,X9) | r2_orders_2(sK6,X8,X7) | ~m1_subset_1(X7,k2_struct_0(sK6)) | ~sP3(X8,sK6,X9)) )),
% 0.21/0.51    inference(superposition,[],[f83,f127])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~sP3(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r2_orders_2(X1,X0,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f52,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r2_orders_2(X1,X0,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  % (26034)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r2_orders_2(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X3,X1,X2] : ((sP3(X3,X1,X2) | ? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X3,X1,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f32])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (26041)------------------------------
% 0.21/0.51  % (26041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (26041)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (26041)Memory used [KB]: 1791
% 0.21/0.51  % (26041)Time elapsed: 0.080 s
% 0.21/0.51  % (26041)------------------------------
% 0.21/0.51  % (26041)------------------------------
% 0.21/0.51  % (26047)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (26032)Success in time 0.144 s
%------------------------------------------------------------------------------
