%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:03 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 961 expanded)
%              Number of leaves         :   11 ( 438 expanded)
%              Depth                    :   19
%              Number of atoms          :  426 (11253 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1445,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1444,f724])).

fof(f724,plain,(
    ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f30,f34,f39,f108,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f108,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f28,f30,f31,f32,f35,f36,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f36,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK1,X2)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
          & m1_pre_topc(X3,sK2)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2)
        & m1_pre_topc(X3,sK2)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
      & m1_pre_topc(sK3,sK2)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f35,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f34,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f1444,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f1405,f709])).

fof(f709,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(forward_demodulation,[],[f708,f313])).

fof(f313,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f312,f28])).

fof(f312,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f311,f30])).

fof(f311,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f310,f31])).

fof(f310,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f309,f32])).

fof(f309,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f308,f35])).

fof(f308,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f307,f36])).

fof(f307,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f306,f96])).

fof(f96,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f28,f30,f31,f32,f35,f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f306,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f305,f108])).

fof(f305,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
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
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f102,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f28,f30,f31,f32,f35,f36,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f708,plain,(
    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(subsumption_resolution,[],[f707,f33])).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f707,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f706,f68])).

fof(f68,plain,(
    l1_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f30,f34,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f706,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f705,f31])).

fof(f705,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f704,f37])).

fof(f37,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f704,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f703,f35])).

fof(f703,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f702,f38])).

fof(f38,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f702,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f701,f143])).

fof(f143,plain,(
    ~ v2_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f33,f68,f31,f37,f35,f38,f47])).

fof(f701,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f700,f151])).

fof(f151,plain,(
    m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2) ),
    inference(unit_resulting_resolution,[],[f33,f68,f31,f37,f35,f38,f49])).

fof(f700,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | ~ m1_pre_topc(sK3,sK2)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f147,f50])).

fof(f147,plain,(
    v1_pre_topc(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f33,f68,f31,f37,f35,f38,f48])).

fof(f1405,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f69,f68,f111,f151,f151,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f111,plain,(
    m1_pre_topc(sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f69,plain,(
    v2_pre_topc(sK2) ),
    inference(unit_resulting_resolution,[],[f29,f30,f34,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (12327)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (12324)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (12333)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (12335)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.49  % (12325)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.50  % (12332)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.31/0.53  % (12321)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.31/0.53  % (12319)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.31/0.53  % (12322)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.31/0.53  % (12323)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 1.31/0.54  % (12329)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.31/0.54  % (12328)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.31/0.54  % (12326)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 1.31/0.54  % (12339)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.31/0.54  % (12336)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.31/0.54  % (12337)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.31/0.54  % (12339)Refutation not found, incomplete strategy% (12339)------------------------------
% 1.31/0.54  % (12339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.54  % (12339)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.54  
% 1.31/0.54  % (12339)Memory used [KB]: 10618
% 1.31/0.54  % (12339)Time elapsed: 0.116 s
% 1.31/0.54  % (12339)------------------------------
% 1.31/0.54  % (12339)------------------------------
% 1.31/0.54  % (12338)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.31/0.54  % (12334)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.31/0.54  % (12320)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (12331)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  % (12320)Refutation not found, incomplete strategy% (12320)------------------------------
% 1.31/0.55  % (12320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (12320)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (12320)Memory used [KB]: 10618
% 1.31/0.55  % (12320)Time elapsed: 0.064 s
% 1.31/0.55  % (12320)------------------------------
% 1.31/0.55  % (12320)------------------------------
% 1.51/0.55  % (12330)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.51/0.56  % (12329)Refutation not found, incomplete strategy% (12329)------------------------------
% 1.51/0.56  % (12329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (12329)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (12329)Memory used [KB]: 6140
% 1.51/0.56  % (12329)Time elapsed: 0.136 s
% 1.51/0.56  % (12329)------------------------------
% 1.51/0.56  % (12329)------------------------------
% 1.51/0.60  % (12334)Refutation found. Thanks to Tanya!
% 1.51/0.60  % SZS status Theorem for theBenchmark
% 1.51/0.60  % SZS output start Proof for theBenchmark
% 1.51/0.60  fof(f1445,plain,(
% 1.51/0.60    $false),
% 1.51/0.60    inference(subsumption_resolution,[],[f1444,f724])).
% 1.51/0.60  fof(f724,plain,(
% 1.51/0.60    ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f29,f30,f34,f39,f108,f45])).
% 1.51/0.60  fof(f45,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f27])).
% 1.51/0.60  fof(f27,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.60    inference(nnf_transformation,[],[f18])).
% 1.51/0.60  fof(f18,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.60    inference(flattening,[],[f17])).
% 1.51/0.60  fof(f17,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.60    inference(ennf_transformation,[],[f6])).
% 1.51/0.60  fof(f6,axiom,(
% 1.51/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.51/0.60  fof(f108,plain,(
% 1.51/0.60    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f28,f30,f31,f32,f35,f36,f49])).
% 1.51/0.60  fof(f49,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f20])).
% 1.51/0.60  fof(f20,plain,(
% 1.51/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.60    inference(flattening,[],[f19])).
% 1.51/0.60  fof(f19,plain,(
% 1.51/0.60    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.60    inference(ennf_transformation,[],[f4])).
% 1.51/0.60  fof(f4,axiom,(
% 1.51/0.60    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.51/0.60  fof(f36,plain,(
% 1.51/0.60    m1_pre_topc(sK3,sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f25,plain,(
% 1.51/0.60    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.51/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f24,f23,f22,f21])).
% 1.51/0.60  fof(f21,plain,(
% 1.51/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.51/0.60    introduced(choice_axiom,[])).
% 1.51/0.60  fof(f22,plain,(
% 1.51/0.60    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.51/0.60    introduced(choice_axiom,[])).
% 1.51/0.60  fof(f23,plain,(
% 1.51/0.60    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.51/0.60    introduced(choice_axiom,[])).
% 1.51/0.60  fof(f24,plain,(
% 1.51/0.60    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.51/0.60    introduced(choice_axiom,[])).
% 1.51/0.60  fof(f10,plain,(
% 1.51/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.51/0.60    inference(flattening,[],[f9])).
% 1.51/0.60  fof(f9,plain,(
% 1.51/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.51/0.60    inference(ennf_transformation,[],[f8])).
% 1.51/0.60  fof(f8,negated_conjecture,(
% 1.51/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 1.51/0.60    inference(negated_conjecture,[],[f7])).
% 1.51/0.60  fof(f7,conjecture,(
% 1.51/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 1.51/0.60  fof(f35,plain,(
% 1.51/0.60    ~v2_struct_0(sK3)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f32,plain,(
% 1.51/0.60    m1_pre_topc(sK1,sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f31,plain,(
% 1.51/0.60    ~v2_struct_0(sK1)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f28,plain,(
% 1.51/0.60    ~v2_struct_0(sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f39,plain,(
% 1.51/0.60    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f34,plain,(
% 1.51/0.60    m1_pre_topc(sK2,sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f30,plain,(
% 1.51/0.60    l1_pre_topc(sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f29,plain,(
% 1.51/0.60    v2_pre_topc(sK0)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f1444,plain,(
% 1.51/0.60    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(sK2))),
% 1.51/0.60    inference(forward_demodulation,[],[f1405,f709])).
% 1.51/0.60  fof(f709,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 1.51/0.60    inference(forward_demodulation,[],[f708,f313])).
% 1.51/0.60  fof(f313,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 1.51/0.60    inference(subsumption_resolution,[],[f312,f28])).
% 1.51/0.60  fof(f312,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f311,f30])).
% 1.51/0.60  fof(f311,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f310,f31])).
% 1.51/0.60  fof(f310,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f309,f32])).
% 1.51/0.60  fof(f309,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f308,f35])).
% 1.51/0.60  fof(f308,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f307,f36])).
% 1.51/0.60  fof(f307,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f306,f96])).
% 1.51/0.60  fof(f96,plain,(
% 1.51/0.60    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f28,f30,f31,f32,f35,f36,f47])).
% 1.51/0.60  fof(f47,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f20])).
% 1.51/0.60  fof(f306,plain,(
% 1.51/0.60    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(subsumption_resolution,[],[f305,f108])).
% 1.51/0.60  fof(f305,plain,(
% 1.51/0.60    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 1.51/0.60    inference(resolution,[],[f102,f50])).
% 1.51/0.60  fof(f50,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.60    inference(equality_resolution,[],[f42])).
% 1.51/0.60  fof(f42,plain,(
% 1.51/0.60    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f26])).
% 1.51/0.60  fof(f26,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.60    inference(nnf_transformation,[],[f14])).
% 1.51/0.60  fof(f14,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.60    inference(flattening,[],[f13])).
% 1.51/0.60  fof(f13,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.60    inference(ennf_transformation,[],[f3])).
% 1.51/0.60  fof(f3,axiom,(
% 1.51/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 1.51/0.60  fof(f102,plain,(
% 1.51/0.60    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3))),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f28,f30,f31,f32,f35,f36,f48])).
% 1.51/0.60  fof(f48,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f20])).
% 1.51/0.60  fof(f708,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 1.51/0.60    inference(subsumption_resolution,[],[f707,f33])).
% 1.51/0.60  fof(f33,plain,(
% 1.51/0.60    ~v2_struct_0(sK2)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f707,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f706,f68])).
% 1.51/0.60  fof(f68,plain,(
% 1.51/0.60    l1_pre_topc(sK2)),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f30,f34,f41])).
% 1.51/0.60  fof(f41,plain,(
% 1.51/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f12])).
% 1.51/0.60  fof(f12,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.51/0.60    inference(ennf_transformation,[],[f2])).
% 1.51/0.60  fof(f2,axiom,(
% 1.51/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.51/0.60  fof(f706,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f705,f31])).
% 1.51/0.60  fof(f705,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f704,f37])).
% 1.51/0.60  fof(f37,plain,(
% 1.51/0.60    m1_pre_topc(sK1,sK2)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f704,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f703,f35])).
% 1.51/0.60  fof(f703,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f702,f38])).
% 1.51/0.60  fof(f38,plain,(
% 1.51/0.60    m1_pre_topc(sK3,sK2)),
% 1.51/0.60    inference(cnf_transformation,[],[f25])).
% 1.51/0.60  fof(f702,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f701,f143])).
% 1.51/0.60  fof(f143,plain,(
% 1.51/0.60    ~v2_struct_0(k1_tsep_1(sK2,sK1,sK3))),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f33,f68,f31,f37,f35,f38,f47])).
% 1.51/0.60  fof(f701,plain,(
% 1.51/0.60    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(subsumption_resolution,[],[f700,f151])).
% 1.51/0.60  fof(f151,plain,(
% 1.51/0.60    m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f33,f68,f31,f37,f35,f38,f49])).
% 1.51/0.60  fof(f700,plain,(
% 1.51/0.60    ~m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) | v2_struct_0(k1_tsep_1(sK2,sK1,sK3)) | ~m1_pre_topc(sK3,sK2) | v2_struct_0(sK3) | ~m1_pre_topc(sK1,sK2) | v2_struct_0(sK1) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.51/0.60    inference(resolution,[],[f147,f50])).
% 1.51/0.60  fof(f147,plain,(
% 1.51/0.60    v1_pre_topc(k1_tsep_1(sK2,sK1,sK3))),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f33,f68,f31,f37,f35,f38,f48])).
% 1.51/0.60  fof(f1405,plain,(
% 1.51/0.60    r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK1,sK3)),u1_struct_0(sK2))),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f69,f68,f111,f151,f151,f46])).
% 1.51/0.60  fof(f46,plain,(
% 1.51/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~v2_pre_topc(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f27])).
% 1.51/0.60  fof(f111,plain,(
% 1.51/0.60    m1_pre_topc(sK2,sK2)),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f68,f40])).
% 1.51/0.60  fof(f40,plain,(
% 1.51/0.60    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f11])).
% 1.51/0.60  fof(f11,plain,(
% 1.51/0.60    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 1.51/0.60    inference(ennf_transformation,[],[f5])).
% 1.51/0.60  fof(f5,axiom,(
% 1.51/0.60    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 1.51/0.60  fof(f69,plain,(
% 1.51/0.60    v2_pre_topc(sK2)),
% 1.51/0.60    inference(unit_resulting_resolution,[],[f29,f30,f34,f44])).
% 1.51/0.60  fof(f44,plain,(
% 1.51/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~v2_pre_topc(X0)) )),
% 1.51/0.60    inference(cnf_transformation,[],[f16])).
% 1.51/0.60  fof(f16,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.60    inference(flattening,[],[f15])).
% 1.51/0.60  fof(f15,plain,(
% 1.51/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.60    inference(ennf_transformation,[],[f1])).
% 1.51/0.60  fof(f1,axiom,(
% 1.51/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.51/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.51/0.60  % SZS output end Proof for theBenchmark
% 1.51/0.60  % (12334)------------------------------
% 1.51/0.60  % (12334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.60  % (12334)Termination reason: Refutation
% 1.51/0.60  
% 1.51/0.60  % (12334)Memory used [KB]: 7547
% 1.51/0.60  % (12334)Time elapsed: 0.151 s
% 1.51/0.60  % (12334)------------------------------
% 1.51/0.60  % (12334)------------------------------
% 1.51/0.61  % (12318)Success in time 0.24 s
%------------------------------------------------------------------------------
