%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:50 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 365 expanded)
%              Number of equality atoms :  169 ( 169 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(resolution,[],[f126,f85])).

fof(f85,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2)) ),
    inference(backward_demodulation,[],[f34,f84])).

fof(f84,plain,(
    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f81,f31])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2))))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2))))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

% (18745)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f12,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).

fof(f81,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f114,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

% (18740)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f114,plain,(
    ! [X7] : r1_tarski(k9_subset_1(u1_struct_0(sK0),X7,sK2),sK2) ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X8,X3,X1] : r2_hidden(X8,k4_enumset1(X0,X1,X2,X3,X4,X8)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X6)
      | k4_enumset1(X0,X1,X2,X3,X4,X8) != X6 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X8,X5,X3,X1] :
      ( r2_hidden(X8,X6)
      | X5 != X8
      | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X5
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
              & sK3(X0,X1,X2,X3,X4,X5,X6) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
          & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X5
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
            | sK3(X0,X1,X2,X3,X4,X5,X6) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X7] :
          ( ( ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 )
            | ~ r2_hidden(X7,X6) )
          & ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7
            | r2_hidden(X7,X6) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5,X6) != X5
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X4
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X3
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X2
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X1
            & sK3(X0,X1,X2,X3,X4,X5,X6) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) )
        & ( sK3(X0,X1,X2,X3,X4,X5,X6) = X5
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X4
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X3
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X2
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X1
          | sK3(X0,X1,X2,X3,X4,X5,X6) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X6)
              | ( X5 != X8
                & X4 != X8
                & X3 != X8
                & X2 != X8
                & X1 != X8
                & X0 != X8 ) )
            & ( X5 = X8
              | X4 = X8
              | X3 = X8
              | X2 = X8
              | X1 = X8
              | X0 = X8
              | ~ r2_hidden(X8,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
        | ? [X7] :
            ( ( ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 )
              | ~ r2_hidden(X7,X6) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | r2_hidden(X7,X6) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X6)
              | ( X5 != X7
                & X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X5 = X7
              | X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X6) ) )
        | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6 ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ( X5 = X7
            | X4 = X7
            | X3 = X7
            | X2 = X7
            | X1 = X7
            | X0 = X7 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( k4_enumset1(X0,X1,X2,X3,X4,X5) = X6
    <=> ! [X7] :
          ( r2_hidden(X7,X6)
        <=> ~ ( X5 != X7
              & X4 != X7
              & X3 != X7
              & X2 != X7
              & X1 != X7
              & X0 != X7 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_enumset1(X0,X0,X0,X0,X0,sK2))
      | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X1) ) ),
    inference(superposition,[],[f38,f83])).

fof(f83,plain,(
    ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,sK2)) ),
    inference(resolution,[],[f33,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:02:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.56  % (18738)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (18746)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (18738)Refutation not found, incomplete strategy% (18738)------------------------------
% 0.21/0.56  % (18738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18738)Memory used [KB]: 1663
% 0.21/0.56  % (18738)Time elapsed: 0.133 s
% 0.21/0.56  % (18738)------------------------------
% 0.21/0.56  % (18738)------------------------------
% 0.21/0.57  % (18755)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.57  % (18754)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (18755)Refutation not found, incomplete strategy% (18755)------------------------------
% 0.21/0.57  % (18755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (18755)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (18755)Memory used [KB]: 10618
% 0.21/0.57  % (18755)Time elapsed: 0.132 s
% 0.21/0.57  % (18755)------------------------------
% 0.21/0.57  % (18755)------------------------------
% 0.21/0.58  % (18763)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.58  % (18746)Refutation found. Thanks to Tanya!
% 1.58/0.58  % SZS status Theorem for theBenchmark
% 1.58/0.58  % SZS output start Proof for theBenchmark
% 1.58/0.58  fof(f155,plain,(
% 1.58/0.58    $false),
% 1.58/0.58    inference(resolution,[],[f126,f85])).
% 1.58/0.58  fof(f85,plain,(
% 1.58/0.58    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(sK2))),
% 1.58/0.58    inference(backward_demodulation,[],[f34,f84])).
% 1.58/0.58  fof(f84,plain,(
% 1.58/0.58    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2))),
% 1.58/0.58    inference(subsumption_resolution,[],[f81,f31])).
% 1.58/0.58  fof(f31,plain,(
% 1.58/0.58    l1_pre_topc(sK0)),
% 1.58/0.58    inference(cnf_transformation,[],[f25])).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ((~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.58/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f24,f23,f22])).
% 1.58/0.58  fof(f22,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f23,plain,(
% 1.58/0.58    ? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f24,plain,(
% 1.58/0.58    ? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.58/0.58    introduced(choice_axiom,[])).
% 1.58/0.58  fof(f15,plain,(
% 1.58/0.58    ? [X0] : (? [X1] : (? [X2] : (~m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f13])).
% 1.58/0.58  fof(f13,negated_conjecture,(
% 1.58/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 1.58/0.58    inference(negated_conjecture,[],[f12])).
% 1.58/0.58  % (18745)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.59  fof(f12,conjecture,(
% 1.58/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => m1_subset_1(k9_subset_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X0,X2)))))))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_tops_2)).
% 1.58/0.59  fof(f81,plain,(
% 1.58/0.59    sK2 = u1_struct_0(k1_pre_topc(sK0,sK2)) | ~l1_pre_topc(sK0)),
% 1.58/0.59    inference(resolution,[],[f33,f35])).
% 1.58/0.59  fof(f35,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f16])).
% 1.58/0.59  fof(f16,plain,(
% 1.58/0.59    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.58/0.59    inference(ennf_transformation,[],[f11])).
% 1.58/0.59  fof(f11,axiom,(
% 1.58/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).
% 1.58/0.59  fof(f33,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f34,plain,(
% 1.58/0.59    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(k1_pre_topc(sK0,sK2))))),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f126,plain,(
% 1.58/0.59    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(sK2))) )),
% 1.58/0.59    inference(resolution,[],[f114,f39])).
% 1.58/0.59  fof(f39,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f18])).
% 1.58/0.59  fof(f18,plain,(
% 1.58/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.58/0.59    inference(ennf_transformation,[],[f14])).
% 1.58/0.59  fof(f14,plain,(
% 1.58/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.58/0.59    inference(unused_predicate_definition_removal,[],[f9])).
% 1.58/0.59  fof(f9,axiom,(
% 1.58/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.58/0.59  % (18740)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.59  fof(f114,plain,(
% 1.58/0.59    ( ! [X7] : (r1_tarski(k9_subset_1(u1_struct_0(sK0),X7,sK2),sK2)) )),
% 1.58/0.59    inference(resolution,[],[f105,f65])).
% 1.58/0.59  fof(f65,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,k4_enumset1(X0,X1,X2,X3,X4,X8))) )),
% 1.58/0.59    inference(equality_resolution,[],[f64])).
% 1.58/0.59  fof(f64,plain,(
% 1.58/0.59    ( ! [X6,X4,X2,X0,X8,X3,X1] : (r2_hidden(X8,X6) | k4_enumset1(X0,X1,X2,X3,X4,X8) != X6) )),
% 1.58/0.59    inference(equality_resolution,[],[f51])).
% 1.58/0.59  fof(f51,plain,(
% 1.58/0.59    ( ! [X6,X4,X2,X0,X8,X5,X3,X1] : (r2_hidden(X8,X6) | X5 != X8 | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6) )),
% 1.58/0.59    inference(cnf_transformation,[],[f30])).
% 1.58/0.59  fof(f30,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | (((sK3(X0,X1,X2,X3,X4,X5,X6) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.58/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 1.58/0.59  fof(f29,plain,(
% 1.58/0.59    ! [X6,X5,X4,X3,X2,X1,X0] : (? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6))) => (((sK3(X0,X1,X2,X3,X4,X5,X6) != X5 & sK3(X0,X1,X2,X3,X4,X5,X6) != X4 & sK3(X0,X1,X2,X3,X4,X5,X6) != X3 & sK3(X0,X1,X2,X3,X4,X5,X6) != X2 & sK3(X0,X1,X2,X3,X4,X5,X6) != X1 & sK3(X0,X1,X2,X3,X4,X5,X6) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6)) & (sK3(X0,X1,X2,X3,X4,X5,X6) = X5 | sK3(X0,X1,X2,X3,X4,X5,X6) = X4 | sK3(X0,X1,X2,X3,X4,X5,X6) = X3 | sK3(X0,X1,X2,X3,X4,X5,X6) = X2 | sK3(X0,X1,X2,X3,X4,X5,X6) = X1 | sK3(X0,X1,X2,X3,X4,X5,X6) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5,X6),X6))))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f28,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X8] : ((r2_hidden(X8,X6) | (X5 != X8 & X4 != X8 & X3 != X8 & X2 != X8 & X1 != X8 & X0 != X8)) & (X5 = X8 | X4 = X8 | X3 = X8 | X2 = X8 | X1 = X8 | X0 = X8 | ~r2_hidden(X8,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.58/0.59    inference(rectify,[],[f27])).
% 1.58/0.59  fof(f27,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.58/0.59    inference(flattening,[],[f26])).
% 1.58/0.59  fof(f26,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : ((k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 | ? [X7] : (((X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7) | ~r2_hidden(X7,X6)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | r2_hidden(X7,X6)))) & (! [X7] : ((r2_hidden(X7,X6) | (X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & ((X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7) | ~r2_hidden(X7,X6))) | k4_enumset1(X0,X1,X2,X3,X4,X5) != X6))),
% 1.58/0.59    inference(nnf_transformation,[],[f21])).
% 1.58/0.59  fof(f21,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> (X5 = X7 | X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7)))),
% 1.58/0.59    inference(ennf_transformation,[],[f6])).
% 1.58/0.59  fof(f6,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5,X6] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = X6 <=> ! [X7] : (r2_hidden(X7,X6) <=> ~(X5 != X7 & X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).
% 1.58/0.59  fof(f105,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k4_enumset1(X0,X0,X0,X0,X0,sK2)) | r1_tarski(k9_subset_1(u1_struct_0(sK0),X0,sK2),X1)) )),
% 1.58/0.59    inference(superposition,[],[f38,f83])).
% 1.58/0.59  fof(f83,plain,(
% 1.58/0.59    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,sK2))) )),
% 1.58/0.59    inference(resolution,[],[f33,f63])).
% 1.58/0.59  fof(f63,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k4_enumset1(X1,X1,X1,X1,X1,X2))) )),
% 1.58/0.59    inference(definition_unfolding,[],[f41,f62])).
% 1.58/0.59  fof(f62,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.58/0.59    inference(definition_unfolding,[],[f36,f61])).
% 1.58/0.59  fof(f61,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f37,f60])).
% 1.58/0.59  fof(f60,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f40,f59])).
% 1.58/0.59  fof(f59,plain,(
% 1.58/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f43,f44])).
% 1.58/0.59  fof(f44,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f4])).
% 1.58/0.59  fof(f4,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.58/0.59  fof(f43,plain,(
% 1.58/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f3])).
% 1.58/0.59  fof(f3,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.58/0.59  fof(f40,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f2])).
% 1.58/0.59  fof(f2,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.59  fof(f37,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f1])).
% 1.58/0.59  fof(f1,axiom,(
% 1.58/0.59    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.59  fof(f36,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f8])).
% 1.58/0.59  fof(f8,axiom,(
% 1.58/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.58/0.59  fof(f41,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f19])).
% 1.58/0.59  fof(f19,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.58/0.59    inference(ennf_transformation,[],[f7])).
% 1.58/0.59  fof(f7,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.58/0.59  fof(f38,plain,(
% 1.58/0.59    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f17])).
% 1.58/0.59  fof(f17,plain,(
% 1.58/0.59    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.58/0.59    inference(ennf_transformation,[],[f10])).
% 1.58/0.59  fof(f10,axiom,(
% 1.58/0.59    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.58/0.59  % SZS output end Proof for theBenchmark
% 1.58/0.59  % (18746)------------------------------
% 1.58/0.59  % (18746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (18746)Termination reason: Refutation
% 1.58/0.59  
% 1.58/0.59  % (18746)Memory used [KB]: 10874
% 1.58/0.59  % (18746)Time elapsed: 0.144 s
% 1.58/0.59  % (18746)------------------------------
% 1.58/0.59  % (18746)------------------------------
% 1.58/0.59  % (18737)Success in time 0.226 s
%------------------------------------------------------------------------------
