%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 290 expanded)
%              Number of leaves         :   16 (  87 expanded)
%              Depth                    :   16
%              Number of atoms          :  314 (1807 expanded)
%              Number of equality atoms :   26 ( 202 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f193,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f170,f183,f85])).

fof(f85,plain,(
    ! [X2] :
      ( r2_hidden(sK7(X2,sK1),sK0)
      | ~ r2_xboole_0(X2,sK1) ) ),
    inference(resolution,[],[f76,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(sK7(X0,X1),X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(sK7(X0,X1),X0)
        & r2_hidden(sK7(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f76,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK0) ) ),
    inference(forward_demodulation,[],[f75,f42])).

fof(f42,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK0)))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f63,f60])).

fof(f60,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(X6,X0)
      | r2_hidden(X5,k3_tarski(X0))
      | ~ r2_hidden(X5,X6) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK4(X0,X1),X3) )
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( ( r2_hidden(sK5(X0,X1),X0)
              & r2_hidden(sK4(X0,X1),sK5(X0,X1)) )
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK6(X0,X5),X0)
                & r2_hidden(X5,sK6(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK4(X0,X1),X3) )
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK4(X0,X1),X4) )
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK4(X0,X1),X4) )
     => ( r2_hidden(sK5(X0,X1),X0)
        & r2_hidden(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK6(X0,X5),X0)
        & r2_hidden(X5,sK6(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f63,plain,(
    r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f41,f36,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != sK2
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK1)
            | ~ r2_hidden(X3,sK2) )
          & ( r2_hidden(X3,sK2)
            | ~ r2_hidden(X3,sK1) ) )
        | ~ m1_subset_1(X3,sK0) )
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).

% (11826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
fof(f22,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( X1 != X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X1)
                    | ~ r2_hidden(X3,X2) )
                  & ( r2_hidden(X3,X2)
                    | ~ r2_hidden(X3,X1) ) )
                | ~ m1_subset_1(X3,X0) )
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( sK1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,sK1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,sK1) ) )
              | ~ m1_subset_1(X3,sK0) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( sK1 != X2
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK1)
                | ~ r2_hidden(X3,X2) )
              & ( r2_hidden(X3,X2)
                | ~ r2_hidden(X3,sK1) ) )
            | ~ m1_subset_1(X3,sK0) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( sK1 != sK2
      & ! [X3] :
          ( ( ( r2_hidden(X3,sK1)
              | ~ r2_hidden(X3,sK2) )
            & ( r2_hidden(X3,sK2)
              | ~ r2_hidden(X3,sK1) ) )
          | ~ m1_subset_1(X3,sK0) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X1)
                  | ~ r2_hidden(X3,X2) )
                & ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X3,X1) ) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & ! [X3] :
              ( ( r2_hidden(X3,X1)
              <=> r2_hidden(X3,X2) )
              | ~ m1_subset_1(X3,X0) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => ( r2_hidden(X3,X1)
                  <=> r2_hidden(X3,X2) ) )
             => X1 = X2 ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).

fof(f41,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f183,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(unit_resulting_resolution,[],[f172,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f172,plain,(
    v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f170,f130])).

fof(f130,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | v1_xboole_0(sK0) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( v1_xboole_0(sK0)
    | ~ r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f94,f57])).

fof(f94,plain,(
    ! [X5] :
      ( ~ r2_hidden(sK7(sK2,X5),sK1)
      | v1_xboole_0(sK0)
      | ~ r2_xboole_0(sK2,X5) ) ),
    inference(resolution,[],[f78,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK1)
      | v1_xboole_0(sK0) ) ),
    inference(subsumption_resolution,[],[f77,f76])).

fof(f77,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2)
      | ~ r2_hidden(X0,sK0)
      | v1_xboole_0(sK0) ) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f38,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK1)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f170,plain,(
    r2_xboole_0(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f40,f169,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f169,plain,(
    r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f168,f37])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f168,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | r1_tarski(sK2,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f106,f112])).

fof(f112,plain,
    ( r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f65,f37])).

fof(f65,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r1_tarski(X1,sK1)
      | r2_hidden(sK3(sK0,X1,sK1),X1) ) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK3(X0,X1,X2),X2)
            & r2_hidden(sK3(X0,X1,X2),X1)
            & m1_subset_1(sK3(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,X0,sK1),sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f103,f66])).

fof(f66,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(sK0,X2,sK1),sK1)
      | r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f103,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | ~ r2_hidden(sK3(sK0,X0,sK1),sK2)
      | r2_hidden(sK3(sK0,X0,sK1),sK1) ) ),
    inference(resolution,[],[f64,f39])).

fof(f39,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,sK0)
      | ~ r2_hidden(X3,sK2)
      | r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(sK0,X0,sK1),sK0)
      | r1_tarski(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK3(X0,X1,X2),X0)
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f40,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (11829)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (11828)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (11820)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (11822)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.48  % (11824)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (11823)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (11835)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (11827)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.48  % (11821)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (11832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (11825)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.49  % (11834)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (11821)Refutation not found, incomplete strategy% (11821)------------------------------
% 0.20/0.49  % (11821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11821)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (11821)Memory used [KB]: 10618
% 0.20/0.49  % (11821)Time elapsed: 0.072 s
% 0.20/0.49  % (11821)------------------------------
% 0.20/0.49  % (11821)------------------------------
% 0.20/0.49  % (11840)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (11835)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f170,f183,f85])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    ( ! [X2] : (r2_hidden(sK7(X2,sK1),sK0) | ~r2_xboole_0(X2,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f76,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1] : ((~r2_hidden(sK7(X0,X1),X0) & r2_hidden(sK7(X0,X1),X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f19,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) => (~r2_hidden(sK7(X0,X1),X0) & r2_hidden(sK7(X0,X1),X1)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f75,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,k3_tarski(k1_zfmisc_1(sK0))) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.49    inference(resolution,[],[f63,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X6,X0,X5] : (~r2_hidden(X6,X0) | r2_hidden(X5,k3_tarski(X0)) | ~r2_hidden(X5,X6)) )),
% 0.20/0.49    inference(equality_resolution,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | k3_tarski(X0) != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & ((r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))) | r2_hidden(sK4(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f29,f32,f31,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK4(X0,X1),X3)) | ~r2_hidden(sK4(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) | r2_hidden(sK4(X0,X1),X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK4(X0,X1),X4)) => (r2_hidden(sK5(X0,X1),X0) & r2_hidden(sK4(X0,X1),sK5(X0,X1))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK6(X0,X5),X0) & r2_hidden(X5,sK6(X0,X5))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.49    inference(rectify,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0,X1] : ((k3_tarski(X0) = X1 | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | k3_tarski(X0) != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f41,f36,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f23,f22])).
% 0.20/0.49  % (11826)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X2] : (sK1 != X2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (sK1 != sK2 & ! [X3] : (((r2_hidden(X3,sK1) | ~r2_hidden(X3,sK2)) & (r2_hidden(X3,sK2) | ~r2_hidden(X3,sK1))) | ~m1_subset_1(X3,sK0)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X2) | ~r2_hidden(X3,X1))) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : (X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ? [X0,X1] : (? [X2] : ((X1 != X2 & ! [X3] : ((r2_hidden(X3,X1) <=> r2_hidden(X3,X2)) | ~m1_subset_1(X3,X0))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.49    inference(negated_conjecture,[],[f9])).
% 0.20/0.49  fof(f9,conjecture,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f172,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    v1_xboole_0(sK0)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f170,f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ~r2_xboole_0(sK2,sK1) | v1_xboole_0(sK0)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    v1_xboole_0(sK0) | ~r2_xboole_0(sK2,sK1) | ~r2_xboole_0(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f94,f57])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X5] : (~r2_hidden(sK7(sK2,X5),sK1) | v1_xboole_0(sK0) | ~r2_xboole_0(sK2,X5)) )),
% 0.20/0.49    inference(resolution,[],[f78,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X0) | ~r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X0] : (r2_hidden(X0,sK2) | ~r2_hidden(X0,sK1) | v1_xboole_0(sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f76])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2) | ~r2_hidden(X0,sK0) | v1_xboole_0(sK0)) )),
% 0.20/0.49    inference(resolution,[],[f38,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f25])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK1) | r2_hidden(X3,sK2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    r2_xboole_0(sK2,sK1)),
% 0.20/0.49    inference(unit_resulting_resolution,[],[f40,f169,f50])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.20/0.49    inference(unused_predicate_definition_removal,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    r1_tarski(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f168,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f166])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f106,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK2,sK1),sK2) | r1_tarski(sK2,sK1)),
% 0.20/0.49    inference(resolution,[],[f65,f37])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK0)) | r1_tarski(X1,sK1) | r2_hidden(sK3(sK0,X1,sK1),X1)) )),
% 0.20/0.49    inference(resolution,[],[f36,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X1) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),X0)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_subset_1)).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (~r2_hidden(sK3(sK0,X0,sK1),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK1)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f66])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    ( ! [X2] : (~r2_hidden(sK3(sK0,X2,sK1),sK1) | r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f36,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X2) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | ~r2_hidden(sK3(sK0,X0,sK1),sK2) | r2_hidden(sK3(sK0,X0,sK1),sK1)) )),
% 0.20/0.49    inference(resolution,[],[f64,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X3] : (~m1_subset_1(X3,sK0) | ~r2_hidden(X3,sK2) | r2_hidden(X3,sK1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK3(sK0,X0,sK1),sK0) | r1_tarski(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(sK0))) )),
% 0.20/0.49    inference(resolution,[],[f36,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK3(X0,X1,X2),X0) | r1_tarski(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f27])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    sK1 != sK2),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (11835)------------------------------
% 0.20/0.49  % (11835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11835)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (11835)Memory used [KB]: 6268
% 0.20/0.49  % (11835)Time elapsed: 0.035 s
% 0.20/0.49  % (11835)------------------------------
% 0.20/0.49  % (11835)------------------------------
% 0.20/0.49  % (11815)Success in time 0.135 s
%------------------------------------------------------------------------------
