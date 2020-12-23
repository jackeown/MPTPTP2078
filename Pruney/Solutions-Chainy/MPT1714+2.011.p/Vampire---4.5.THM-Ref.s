%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (1083 expanded)
%              Number of leaves         :   21 ( 362 expanded)
%              Depth                    :   26
%              Number of atoms          :  519 (8701 expanded)
%              Number of equality atoms :   28 (  86 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f328,plain,(
    $false ),
    inference(subsumption_resolution,[],[f327,f112])).

fof(f112,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f108,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f108,plain,(
    l1_pre_topc(sK3) ),
    inference(resolution,[],[f107,f60])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( r1_tsep_1(sK5,sK4)
      | r1_tsep_1(sK4,sK5) )
    & ( ~ r1_tsep_1(sK5,sK3)
      | ~ r1_tsep_1(sK3,sK5) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & m1_pre_topc(sK4,sK2)
    & m1_pre_topc(sK3,sK2)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X2,X3) )
                    & ( ~ r1_tsep_1(X3,X1)
                      | ~ r1_tsep_1(X1,X3) )
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0) )
                & m1_pre_topc(X2,X0) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK2) )
              & m1_pre_topc(X2,sK2) )
          & m1_pre_topc(X1,sK2) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X2,X3) )
                & ( ~ r1_tsep_1(X3,X1)
                  | ~ r1_tsep_1(X1,X3) )
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK2) )
            & m1_pre_topc(X2,sK2) )
        & m1_pre_topc(X1,sK2) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( r1_tsep_1(X3,X2)
                | r1_tsep_1(X2,X3) )
              & ( ~ r1_tsep_1(X3,sK3)
                | ~ r1_tsep_1(sK3,X3) )
              & m1_pre_topc(sK3,X2)
              & m1_pre_topc(X3,sK2) )
          & m1_pre_topc(X2,sK2) )
      & m1_pre_topc(sK3,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( r1_tsep_1(X3,X2)
              | r1_tsep_1(X2,X3) )
            & ( ~ r1_tsep_1(X3,sK3)
              | ~ r1_tsep_1(sK3,X3) )
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X3,sK2) )
        & m1_pre_topc(X2,sK2) )
   => ( ? [X3] :
          ( ( r1_tsep_1(X3,sK4)
            | r1_tsep_1(sK4,X3) )
          & ( ~ r1_tsep_1(X3,sK3)
            | ~ r1_tsep_1(sK3,X3) )
          & m1_pre_topc(sK3,sK4)
          & m1_pre_topc(X3,sK2) )
      & m1_pre_topc(sK4,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ( r1_tsep_1(X3,sK4)
          | r1_tsep_1(sK4,X3) )
        & ( ~ r1_tsep_1(X3,sK3)
          | ~ r1_tsep_1(sK3,X3) )
        & m1_pre_topc(sK3,sK4)
        & m1_pre_topc(X3,sK2) )
   => ( ( r1_tsep_1(sK5,sK4)
        | r1_tsep_1(sK4,sK5) )
      & ( ~ r1_tsep_1(sK5,sK3)
        | ~ r1_tsep_1(sK3,sK5) )
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK5,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
                  & ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0) )
              & m1_pre_topc(X2,X0) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ! [X3] :
                    ( m1_pre_topc(X3,X0)
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( m1_pre_topc(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) )
                        | ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f107,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f82,f59])).

fof(f59,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f327,plain,(
    ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f326,f116])).

fof(f116,plain,(
    l1_struct_0(sK5) ),
    inference(resolution,[],[f110,f69])).

fof(f110,plain,(
    l1_pre_topc(sK5) ),
    inference(resolution,[],[f107,f62])).

fof(f62,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f326,plain,
    ( ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f321,f318])).

fof(f318,plain,(
    ~ r1_tsep_1(sK5,sK3) ),
    inference(subsumption_resolution,[],[f64,f317])).

fof(f317,plain,(
    r1_tsep_1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f204,f316])).

fof(f316,plain,(
    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5)) ),
    inference(duplicate_literal_removal,[],[f314])).

fof(f314,plain,
    ( r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5))
    | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5)) ),
    inference(resolution,[],[f312,f163])).

fof(f163,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK9(X1,k2_struct_0(sK5)),k2_struct_0(sK4))
      | r1_xboole_0(X1,k2_struct_0(sK5)) ) ),
    inference(resolution,[],[f150,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f150,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK5))
      | ~ r2_hidden(X0,k2_struct_0(sK4)) ) ),
    inference(resolution,[],[f145,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f145,plain,(
    r1_xboole_0(k2_struct_0(sK4),k2_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f144,f118])).

fof(f118,plain,(
    u1_struct_0(sK4) = k2_struct_0(sK4) ),
    inference(resolution,[],[f114,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f114,plain,(
    l1_struct_0(sK4) ),
    inference(resolution,[],[f109,f69])).

fof(f109,plain,(
    l1_pre_topc(sK4) ),
    inference(resolution,[],[f107,f61])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f144,plain,(
    r1_xboole_0(u1_struct_0(sK4),k2_struct_0(sK5)) ),
    inference(forward_demodulation,[],[f143,f119])).

fof(f119,plain,(
    u1_struct_0(sK5) = k2_struct_0(sK5) ),
    inference(resolution,[],[f116,f66])).

fof(f143,plain,(
    r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    inference(subsumption_resolution,[],[f142,f114])).

fof(f142,plain,
    ( r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f140,f116])).

fof(f140,plain,
    ( r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4) ),
    inference(resolution,[],[f67,f127])).

fof(f127,plain,(
    r1_tsep_1(sK4,sK5) ),
    inference(subsumption_resolution,[],[f126,f116])).

fof(f126,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK5) ),
    inference(subsumption_resolution,[],[f125,f114])).

fof(f125,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,
    ( r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | ~ l1_struct_0(sK5)
    | r1_tsep_1(sK4,sK5) ),
    inference(resolution,[],[f87,f65])).

fof(f65,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f312,plain,(
    ! [X0] :
      ( r2_hidden(sK9(k2_struct_0(sK3),X0),k2_struct_0(sK4))
      | r1_xboole_0(k2_struct_0(sK3),X0) ) ),
    inference(resolution,[],[f304,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f304,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_struct_0(sK3))
      | r2_hidden(X2,k2_struct_0(sK4)) ) ),
    inference(superposition,[],[f133,f298])).

fof(f298,plain,(
    k2_struct_0(sK4) = k2_xboole_0(k2_struct_0(sK4),k2_struct_0(sK3)) ),
    inference(resolution,[],[f248,f63])).

fof(f63,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f248,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(X2,sK4)
      | k2_struct_0(sK4) = k2_xboole_0(k2_struct_0(sK4),k2_struct_0(X2)) ) ),
    inference(resolution,[],[f207,f109])).

fof(f207,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1)
      | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f205,f82])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0)) ) ),
    inference(resolution,[],[f78,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(subsumption_resolution,[],[f134,f102])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X1)
      | k2_xboole_0(X1,X0) = X1 ) ),
    inference(resolution,[],[f91,f122])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X2),X1)
      | k2_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f90,f83])).

fof(f83,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ~ sP0(sK8(X0,X1),X1,X0)
                & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X3] :
                    ( sP0(X3,X1,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ sP0(X2,X1,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ sP0(sK8(X0,X1),X1,X0)
        & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ~ sP0(X2,X1,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X3] :
                    ( sP0(X3,X1,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ~ sP0(X2,X1,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( sP0(X2,X1,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ~ sP0(X2,X1,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( sP0(X2,X1,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( sP0(X2,X1,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f22,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( sP0(X2,X1,X0)
    <=> ( r2_hidden(X2,u1_pre_topc(X1))
      <=> ? [X3] :
            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
            & r2_hidden(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X2,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f94,f104])).

fof(f104,plain,(
    ! [X0,X1] : sP1(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK10(X0,X1,X2),X0)
              & ~ r2_hidden(sK10(X0,X1,X2),X1) )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( r2_hidden(sK10(X0,X1,X2),X0)
            | r2_hidden(sK10(X0,X1,X2),X1)
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK10(X0,X1,X2),X0)
            & ~ r2_hidden(sK10(X0,X1,X2),X1) )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( r2_hidden(sK10(X0,X1,X2),X0)
          | r2_hidden(sK10(X0,X1,X2),X1)
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f204,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5))
    | r1_tsep_1(sK3,sK5) ),
    inference(subsumption_resolution,[],[f200,f116])).

fof(f200,plain,
    ( ~ r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | r1_tsep_1(sK3,sK5) ),
    inference(superposition,[],[f186,f119])).

fof(f186,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | r1_tsep_1(sK3,X1) ) ),
    inference(forward_demodulation,[],[f182,f117])).

fof(f117,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f112,f66])).

fof(f182,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(u1_struct_0(sK3),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | r1_tsep_1(sK3,X1) ) ),
    inference(resolution,[],[f68,f112])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,
    ( ~ r1_tsep_1(sK5,sK3)
    | ~ r1_tsep_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f321,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK3) ),
    inference(resolution,[],[f317,f87])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (23953)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (23940)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (23948)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (23940)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f328,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f327,f112])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    l1_struct_0(sK3)),
% 0.21/0.51    inference(resolution,[],[f108,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    l1_pre_topc(sK3)),
% 0.21/0.51    inference(resolution,[],[f107,f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ((((r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & (~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2)) & m1_pre_topc(sK4,sK2)) & m1_pre_topc(sK3,sK2)) & l1_pre_topc(sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f18,f36,f35,f34,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) & l1_pre_topc(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(X1,sK2)) => (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) & m1_pre_topc(sK3,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2)) & m1_pre_topc(X2,sK2)) => (? [X3] : ((r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2)) & m1_pre_topc(sK4,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ? [X3] : ((r1_tsep_1(X3,sK4) | r1_tsep_1(sK4,X3)) & (~r1_tsep_1(X3,sK3) | ~r1_tsep_1(sK3,X3)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2)) => ((r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)) & (~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & (~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3))) & m1_pre_topc(X1,X2)) & m1_pre_topc(X3,X0)) & m1_pre_topc(X2,X0)) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.51    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.51  fof(f13,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f12])).
% 0.21/0.51  fof(f12,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_pre_topc(X0,sK2) | l1_pre_topc(X0)) )),
% 0.21/0.51    inference(resolution,[],[f82,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    l1_pre_topc(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    ~l1_struct_0(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f326,f116])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    l1_struct_0(sK5)),
% 0.21/0.51    inference(resolution,[],[f110,f69])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    l1_pre_topc(sK5)),
% 0.21/0.51    inference(resolution,[],[f107,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    m1_pre_topc(sK5,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    ~l1_struct_0(sK5) | ~l1_struct_0(sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f321,f318])).
% 0.21/0.51  fof(f318,plain,(
% 0.21/0.51    ~r1_tsep_1(sK5,sK3)),
% 0.21/0.51    inference(subsumption_resolution,[],[f64,f317])).
% 0.21/0.51  fof(f317,plain,(
% 0.21/0.51    r1_tsep_1(sK3,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f204,f316])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f314])).
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5)) | r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5))),
% 0.21/0.51    inference(resolution,[],[f312,f163])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    ( ! [X1] : (~r2_hidden(sK9(X1,k2_struct_0(sK5)),k2_struct_0(sK4)) | r1_xboole_0(X1,k2_struct_0(sK5))) )),
% 0.21/0.51    inference(resolution,[],[f150,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f150,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK5)) | ~r2_hidden(X0,k2_struct_0(sK4))) )),
% 0.21/0.51    inference(resolution,[],[f145,f86])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    r1_xboole_0(k2_struct_0(sK4),k2_struct_0(sK5))),
% 0.21/0.51    inference(forward_demodulation,[],[f144,f118])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    u1_struct_0(sK4) = k2_struct_0(sK4)),
% 0.21/0.51    inference(resolution,[],[f114,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    l1_struct_0(sK4)),
% 0.21/0.51    inference(resolution,[],[f109,f69])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    l1_pre_topc(sK4)),
% 0.21/0.51    inference(resolution,[],[f107,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    m1_pre_topc(sK4,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    r1_xboole_0(u1_struct_0(sK4),k2_struct_0(sK5))),
% 0.21/0.51    inference(forward_demodulation,[],[f143,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    u1_struct_0(sK5) = k2_struct_0(sK5)),
% 0.21/0.51    inference(resolution,[],[f116,f66])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f114])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_struct_0(sK4)),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f116])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    r1_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) | ~l1_struct_0(sK5) | ~l1_struct_0(sK4)),
% 0.21/0.51    inference(resolution,[],[f67,f127])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    r1_tsep_1(sK4,sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f116])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    r1_tsep_1(sK4,sK5) | ~l1_struct_0(sK5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f114])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    r1_tsep_1(sK4,sK5) | ~l1_struct_0(sK4) | ~l1_struct_0(sK5)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    r1_tsep_1(sK4,sK5) | ~l1_struct_0(sK4) | ~l1_struct_0(sK5) | r1_tsep_1(sK4,sK5)),
% 0.21/0.51    inference(resolution,[],[f87,f65])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    r1_tsep_1(sK5,sK4) | r1_tsep_1(sK4,sK5)),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    ( ! [X0] : (r2_hidden(sK9(k2_struct_0(sK3),X0),k2_struct_0(sK4)) | r1_xboole_0(k2_struct_0(sK3),X0)) )),
% 0.21/0.51    inference(resolution,[],[f304,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    ( ! [X2] : (~r2_hidden(X2,k2_struct_0(sK3)) | r2_hidden(X2,k2_struct_0(sK4))) )),
% 0.21/0.51    inference(superposition,[],[f133,f298])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    k2_struct_0(sK4) = k2_xboole_0(k2_struct_0(sK4),k2_struct_0(sK3))),
% 0.21/0.51    inference(resolution,[],[f248,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    m1_pre_topc(sK3,sK4)),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    ( ! [X2] : (~m1_pre_topc(X2,sK4) | k2_struct_0(sK4) = k2_xboole_0(k2_struct_0(sK4),k2_struct_0(X2))) )),
% 0.21/0.51    inference(resolution,[],[f207,f109])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1) | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f205,f82])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | k2_struct_0(X1) = k2_xboole_0(k2_struct_0(X1),k2_struct_0(X0))) )),
% 0.21/0.51    inference(resolution,[],[f78,f136])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X1,X0) = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X1) | k2_xboole_0(X1,X0) = X1) )),
% 0.21/0.52    inference(resolution,[],[f91,f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    ( ! [X2,X1] : (~r1_tarski(k2_xboole_0(X1,X2),X1) | k2_xboole_0(X1,X2) = X1) )),
% 0.21/0.52    inference(resolution,[],[f90,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f52])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (~sP0(sK8(X0,X1),X1,X0) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X3] : (sP0(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f46,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => (~sP0(sK8(X0,X1),X1,X0) & m1_subset_1(sK8(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X3] : (sP0(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (~sP0(X2,X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : (sP0(X2,X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(definition_folding,[],[f22,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (sP0(X2,X1,X0) <=> (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,k2_xboole_0(X2,X1)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(resolution,[],[f94,f104])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    ( ! [X0,X1] : (sP1(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.52    inference(nnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 0.21/0.52    inference(definition_folding,[],[f1,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (((~r2_hidden(sK10(X0,X1,X2),X0) & ~r2_hidden(sK10(X0,X1,X2),X1)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (r2_hidden(sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X1) | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f55,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK10(X0,X1,X2),X0) & ~r2_hidden(sK10(X0,X1,X2),X1)) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (r2_hidden(sK10(X0,X1,X2),X0) | r2_hidden(sK10(X0,X1,X2),X1) | r2_hidden(sK10(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP1(X0,X1,X2)))),
% 0.21/0.52    inference(rectify,[],[f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.52    inference(flattening,[],[f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP1(X1,X0,X2)))),
% 0.21/0.52    inference(nnf_transformation,[],[f31])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5)) | r1_tsep_1(sK3,sK5)),
% 0.21/0.52    inference(subsumption_resolution,[],[f200,f116])).
% 0.21/0.52  fof(f200,plain,(
% 0.21/0.52    ~r1_xboole_0(k2_struct_0(sK3),k2_struct_0(sK5)) | ~l1_struct_0(sK5) | r1_tsep_1(sK3,sK5)),
% 0.21/0.52    inference(superposition,[],[f186,f119])).
% 0.21/0.52  fof(f186,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_xboole_0(k2_struct_0(sK3),u1_struct_0(X1)) | ~l1_struct_0(X1) | r1_tsep_1(sK3,X1)) )),
% 0.21/0.52    inference(forward_demodulation,[],[f182,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f112,f66])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_xboole_0(u1_struct_0(sK3),u1_struct_0(X1)) | ~l1_struct_0(X1) | r1_tsep_1(sK3,X1)) )),
% 0.21/0.52    inference(resolution,[],[f68,f112])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_struct_0(X0) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | r1_tsep_1(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~r1_tsep_1(sK5,sK3) | ~r1_tsep_1(sK3,sK5)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f321,plain,(
% 0.21/0.52    r1_tsep_1(sK5,sK3) | ~l1_struct_0(sK5) | ~l1_struct_0(sK3)),
% 0.21/0.52    inference(resolution,[],[f317,f87])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (23940)------------------------------
% 0.21/0.52  % (23940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23940)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (23940)Memory used [KB]: 6396
% 0.21/0.52  % (23940)Time elapsed: 0.068 s
% 0.21/0.52  % (23940)------------------------------
% 0.21/0.52  % (23940)------------------------------
% 0.21/0.52  % (23936)Success in time 0.159 s
%------------------------------------------------------------------------------
