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
% DateTime   : Thu Dec  3 13:18:02 EST 2020

% Result     : Theorem 12.25s
% Output     : Refutation 12.25s
% Verified   : 
% Statistics : Number of formulae       :  171 (4040 expanded)
%              Number of leaves         :   14 (2040 expanded)
%              Depth                    :   23
%              Number of atoms          :  854 (56356 expanded)
%              Number of equality atoms :  102 ( 214 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f59063,plain,(
    $false ),
    inference(subsumption_resolution,[],[f59062,f765])).

fof(f765,plain,(
    ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f38,f39,f128,f50,f167,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f167,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f47,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f32,f31,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4))
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4))
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4))
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4))
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4))
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4))
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X4] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4))
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f46,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f33])).

fof(f128,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f62])).

fof(f45,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f59062,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(forward_demodulation,[],[f59058,f1051])).

fof(f1051,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1050,f37])).

fof(f1050,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1049,f39])).

fof(f1049,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1048,f44])).

fof(f1048,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1047,f45])).

fof(f1047,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1046,f40])).

fof(f1046,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1045,f41])).

fof(f1045,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1044,f116])).

fof(f116,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1044,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1043,f128])).

fof(f1043,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1042,f122])).

fof(f122,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1042,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f110])).

fof(f110,plain,(
    k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f64,plain,(
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
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f59058,plain,(
    r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f58055,f58415,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f58415,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f58031,f53266])).

fof(f53266,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK2),X3)
      | r1_tarski(u1_struct_0(sK1),X3) ) ),
    inference(resolution,[],[f14387,f13983])).

fof(f13983,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),X3)
      | r1_tarski(u1_struct_0(sK1),X3) ) ),
    inference(superposition,[],[f58,f207])).

fof(f207,plain,(
    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f206,f37])).

fof(f206,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f205,f39])).

fof(f205,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f204,f40])).

fof(f204,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f203,f41])).

fof(f203,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f202,f42])).

fof(f202,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f201,f43])).

fof(f201,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f200,f93])).

fof(f93,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f42,f43,f60])).

fof(f200,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f199,f101])).

fof(f101,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f42,f43,f62])).

fof(f199,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f97,f64])).

fof(f97,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f42,f43,f61])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f14387,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),X2)
      | ~ r1_tarski(u1_struct_0(sK2),X2) ) ),
    inference(duplicate_literal_removal,[],[f14385])).

fof(f14385,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),X2)
      | ~ r1_tarski(u1_struct_0(sK2),X2)
      | ~ r1_tarski(u1_struct_0(sK2),X2) ) ),
    inference(superposition,[],[f63,f1153])).

fof(f1153,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f1152,f37])).

fof(f1152,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1151,f39])).

fof(f1151,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1150,f42])).

fof(f1150,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1149,f43])).

fof(f1149,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1148,f93])).

fof(f1148,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1147,f101])).

fof(f1147,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1144,f97])).

fof(f1144,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1143])).

fof(f1143,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f181])).

fof(f181,plain,(
    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f86,f179])).

fof(f179,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f42,f41,f43,f48,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f48,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f42,f43,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f58031,plain,(
    r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f52252,f14014])).

fof(f14014,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),X3)
      | r1_tarski(u1_struct_0(sK2),X3) ) ),
    inference(superposition,[],[f58,f251])).

fof(f251,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f250,f37])).

fof(f250,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f249,f39])).

fof(f249,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f42])).

fof(f248,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f247,f43])).

fof(f247,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f246,f46])).

fof(f246,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f245,f47])).

fof(f245,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f244,f151])).

fof(f151,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f60])).

fof(f244,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f167])).

fof(f243,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f159,f64])).

fof(f159,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f61])).

fof(f52252,plain,(
    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f167,f167,f52247,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(subsumption_resolution,[],[f65,f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f38,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f52247,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f151,f151,f167,f167,f763,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f763,plain,(
    g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),u1_pre_topc(k1_tsep_1(sK0,sK2,sK4))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK2,sK4)) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f151,f167,f51])).

fof(f58055,plain,(
    r1_tarski(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f58030,f53276])).

fof(f53276,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(sK4),X3)
      | r1_tarski(u1_struct_0(sK3),X3) ) ),
    inference(resolution,[],[f14394,f14020])).

fof(f14020,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),X3)
      | r1_tarski(u1_struct_0(sK3),X3) ) ),
    inference(superposition,[],[f58,f260])).

fof(f260,plain,(
    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) ),
    inference(subsumption_resolution,[],[f259,f37])).

fof(f259,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f258,f39])).

fof(f258,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f257,f44])).

fof(f257,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f45])).

fof(f256,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f46])).

fof(f255,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f47])).

fof(f254,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f152])).

fof(f152,plain,(
    ~ v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f44,f45,f46,f47,f60])).

fof(f253,plain,
    ( k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f252,f168])).

fof(f168,plain,(
    m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) ),
    inference(unit_resulting_resolution,[],[f37,f39,f44,f45,f46,f47,f62])).

fof(f252,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)
    | k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f64])).

fof(f160,plain,(
    v1_pre_topc(k1_tsep_1(sK0,sK3,sK4)) ),
    inference(unit_resulting_resolution,[],[f37,f39,f44,f45,f46,f47,f61])).

fof(f14394,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),X2)
      | ~ r1_tarski(u1_struct_0(sK4),X2) ) ),
    inference(duplicate_literal_removal,[],[f14392])).

fof(f14392,plain,(
    ! [X2] :
      ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),X2)
      | ~ r1_tarski(u1_struct_0(sK4),X2)
      | ~ r1_tarski(u1_struct_0(sK4),X2) ) ),
    inference(superposition,[],[f63,f1166])).

fof(f1166,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) ),
    inference(subsumption_resolution,[],[f1165,f37])).

fof(f1165,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1164,f39])).

fof(f1164,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1163,f46])).

fof(f1163,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1162,f47])).

fof(f1162,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1161,f152])).

fof(f1161,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1160,f168])).

fof(f1160,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1157,f160])).

fof(f1157,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f1156])).

fof(f1156,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))
    | v2_struct_0(k1_tsep_1(sK0,sK3,sK4))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f187])).

fof(f187,plain,(
    k1_tsep_1(sK0,sK4,sK4) = k1_tsep_1(sK0,sK3,sK4) ),
    inference(backward_demodulation,[],[f137,f185])).

fof(f185,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK0,sK3,sK4) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f44,f46,f45,f47,f49,f52])).

fof(f49,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f137,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK0,sK4,sK4) ),
    inference(unit_resulting_resolution,[],[f37,f38,f39,f46,f47,f51])).

fof(f58030,plain,(
    r1_tarski(u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK0,sK2,sK4))) ),
    inference(unit_resulting_resolution,[],[f52252,f14374])).

fof(f14374,plain,(
    ! [X3] :
      ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),X3)
      | r1_tarski(u1_struct_0(sK4),X3) ) ),
    inference(superposition,[],[f58,f1110])).

fof(f1110,plain,(
    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f1109,f37])).

fof(f1109,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1108,f39])).

fof(f1108,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1107,f46])).

fof(f1107,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1106,f47])).

fof(f1106,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1105,f42])).

fof(f1105,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1104,f43])).

fof(f1104,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1103,f151])).

fof(f1103,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1102,f167])).

fof(f1102,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1101,f159])).

fof(f1101,plain,
    ( ~ v1_pre_topc(k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK4))
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f64,f143])).

fof(f143,plain,(
    k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2) ),
    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (12289)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.43  % (12296)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.46  % (12287)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (12293)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (12303)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (12299)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (12297)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (12288)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (12291)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (12302)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (12295)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (12304)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (12292)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (12308)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (12308)Refutation not found, incomplete strategy% (12308)------------------------------
% 0.21/0.49  % (12308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12308)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12308)Memory used [KB]: 10618
% 0.21/0.49  % (12308)Time elapsed: 0.094 s
% 0.21/0.49  % (12308)------------------------------
% 0.21/0.49  % (12308)------------------------------
% 0.21/0.49  % (12307)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (12301)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (12298)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (12298)Refutation not found, incomplete strategy% (12298)------------------------------
% 0.21/0.50  % (12298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12298)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12298)Memory used [KB]: 6012
% 0.21/0.50  % (12298)Time elapsed: 0.095 s
% 0.21/0.50  % (12298)------------------------------
% 0.21/0.50  % (12298)------------------------------
% 0.21/0.50  % (12288)Refutation not found, incomplete strategy% (12288)------------------------------
% 0.21/0.50  % (12288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (12288)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (12288)Memory used [KB]: 10618
% 0.21/0.50  % (12288)Time elapsed: 0.091 s
% 0.21/0.50  % (12288)------------------------------
% 0.21/0.50  % (12288)------------------------------
% 0.21/0.50  % (12300)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12290)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (12305)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (12306)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 3.74/0.90  % (12300)Time limit reached!
% 3.74/0.90  % (12300)------------------------------
% 3.74/0.90  % (12300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.74/0.90  % (12300)Termination reason: Time limit
% 3.74/0.90  % (12300)Termination phase: Saturation
% 3.74/0.90  
% 3.74/0.90  % (12300)Memory used [KB]: 16886
% 3.74/0.90  % (12300)Time elapsed: 0.505 s
% 3.74/0.90  % (12300)------------------------------
% 3.74/0.90  % (12300)------------------------------
% 4.46/0.92  % (12292)Time limit reached!
% 4.46/0.92  % (12292)------------------------------
% 4.46/0.92  % (12292)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.92  % (12292)Termination reason: Time limit
% 4.46/0.92  
% 4.46/0.92  % (12292)Memory used [KB]: 8699
% 4.46/0.92  % (12292)Time elapsed: 0.524 s
% 4.46/0.92  % (12292)------------------------------
% 4.46/0.92  % (12292)------------------------------
% 4.46/0.93  % (12287)Time limit reached!
% 4.46/0.93  % (12287)------------------------------
% 4.46/0.93  % (12287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.93  % (12287)Termination reason: Time limit
% 4.46/0.93  
% 4.46/0.93  % (12287)Memory used [KB]: 12409
% 4.46/0.93  % (12287)Time elapsed: 0.515 s
% 4.46/0.93  % (12287)------------------------------
% 4.46/0.93  % (12287)------------------------------
% 5.04/1.00  % (12296)Time limit reached!
% 5.04/1.00  % (12296)------------------------------
% 5.04/1.00  % (12296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.04/1.00  % (12296)Termination reason: Time limit
% 5.04/1.00  
% 5.04/1.00  % (12296)Memory used [KB]: 7931
% 5.04/1.00  % (12296)Time elapsed: 0.619 s
% 5.04/1.00  % (12296)------------------------------
% 5.04/1.00  % (12296)------------------------------
% 7.49/1.31  % (12297)Time limit reached!
% 7.49/1.31  % (12297)------------------------------
% 7.49/1.31  % (12297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.49/1.32  % (12297)Termination reason: Time limit
% 7.49/1.32  % (12297)Termination phase: Saturation
% 7.49/1.32  
% 7.49/1.32  % (12297)Memory used [KB]: 21875
% 7.49/1.32  % (12297)Time elapsed: 0.900 s
% 7.49/1.32  % (12297)------------------------------
% 7.49/1.32  % (12297)------------------------------
% 8.59/1.50  % (12289)Time limit reached!
% 8.59/1.50  % (12289)------------------------------
% 8.59/1.50  % (12289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.23/1.50  % (12289)Termination reason: Time limit
% 9.23/1.50  
% 9.23/1.50  % (12289)Memory used [KB]: 19445
% 9.23/1.50  % (12289)Time elapsed: 1.120 s
% 9.23/1.50  % (12289)------------------------------
% 9.23/1.50  % (12289)------------------------------
% 10.93/1.72  % (12290)Time limit reached!
% 10.93/1.72  % (12290)------------------------------
% 10.93/1.72  % (12290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.93/1.72  % (12290)Termination reason: Time limit
% 10.93/1.72  % (12290)Termination phase: Saturation
% 10.93/1.72  
% 10.93/1.72  % (12290)Memory used [KB]: 21236
% 10.93/1.72  % (12290)Time elapsed: 1.300 s
% 10.93/1.72  % (12290)------------------------------
% 10.93/1.72  % (12290)------------------------------
% 12.25/1.94  % (12303)Refutation found. Thanks to Tanya!
% 12.25/1.94  % SZS status Theorem for theBenchmark
% 12.25/1.94  % SZS output start Proof for theBenchmark
% 12.25/1.94  fof(f59063,plain,(
% 12.25/1.94    $false),
% 12.25/1.94    inference(subsumption_resolution,[],[f59062,f765])).
% 12.25/1.94  fof(f765,plain,(
% 12.25/1.94    ~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f38,f39,f128,f50,f167,f56])).
% 12.25/1.94  fof(f56,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f36])).
% 12.25/1.94  fof(f36,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.25/1.94    inference(nnf_transformation,[],[f20])).
% 12.25/1.94  fof(f20,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 12.25/1.94    inference(flattening,[],[f19])).
% 12.25/1.94  fof(f19,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f8])).
% 12.25/1.94  fof(f8,axiom,(
% 12.25/1.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 12.25/1.94  fof(f167,plain,(
% 12.25/1.94    m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f62])).
% 12.25/1.94  fof(f62,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f25])).
% 12.25/1.94  fof(f25,plain,(
% 12.25/1.94    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(flattening,[],[f24])).
% 12.25/1.94  fof(f24,plain,(
% 12.25/1.94    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f5])).
% 12.25/1.94  fof(f5,axiom,(
% 12.25/1.94    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 12.25/1.94  fof(f47,plain,(
% 12.25/1.94    m1_pre_topc(sK4,sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f33,plain,(
% 12.25/1.94    ((((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 12.25/1.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f12,f32,f31,f30,f29,f28])).
% 12.25/1.94  fof(f28,plain,(
% 12.25/1.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 12.25/1.94    introduced(choice_axiom,[])).
% 12.25/1.94  fof(f29,plain,(
% 12.25/1.94    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 12.25/1.94    introduced(choice_axiom,[])).
% 12.25/1.94  fof(f30,plain,(
% 12.25/1.94    ? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 12.25/1.94    introduced(choice_axiom,[])).
% 12.25/1.94  fof(f31,plain,(
% 12.25/1.94    ? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 12.25/1.94    introduced(choice_axiom,[])).
% 12.25/1.94  fof(f32,plain,(
% 12.25/1.94    ? [X4] : (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 12.25/1.94    introduced(choice_axiom,[])).
% 12.25/1.94  fof(f12,plain,(
% 12.25/1.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 12.25/1.94    inference(flattening,[],[f11])).
% 12.25/1.94  fof(f11,plain,(
% 12.25/1.94    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) & (m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f10])).
% 12.25/1.94  fof(f10,negated_conjecture,(
% 12.25/1.94    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 12.25/1.94    inference(negated_conjecture,[],[f9])).
% 12.25/1.94  fof(f9,conjecture,(
% 12.25/1.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_tmap_1)).
% 12.25/1.94  fof(f46,plain,(
% 12.25/1.94    ~v2_struct_0(sK4)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f43,plain,(
% 12.25/1.94    m1_pre_topc(sK2,sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f42,plain,(
% 12.25/1.94    ~v2_struct_0(sK2)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f37,plain,(
% 12.25/1.94    ~v2_struct_0(sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f50,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f128,plain,(
% 12.25/1.94    m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f62])).
% 12.25/1.94  fof(f45,plain,(
% 12.25/1.94    m1_pre_topc(sK3,sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f44,plain,(
% 12.25/1.94    ~v2_struct_0(sK3)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f41,plain,(
% 12.25/1.94    m1_pre_topc(sK1,sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f40,plain,(
% 12.25/1.94    ~v2_struct_0(sK1)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f39,plain,(
% 12.25/1.94    l1_pre_topc(sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f38,plain,(
% 12.25/1.94    v2_pre_topc(sK0)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f59062,plain,(
% 12.25/1.94    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK3)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(forward_demodulation,[],[f59058,f1051])).
% 12.25/1.94  fof(f1051,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1))),
% 12.25/1.94    inference(subsumption_resolution,[],[f1050,f37])).
% 12.25/1.94  fof(f1050,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1049,f39])).
% 12.25/1.94  fof(f1049,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1048,f44])).
% 12.25/1.94  fof(f1048,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1047,f45])).
% 12.25/1.94  fof(f1047,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1046,f40])).
% 12.25/1.94  fof(f1046,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1045,f41])).
% 12.25/1.94  fof(f1045,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1044,f116])).
% 12.25/1.94  fof(f116,plain,(
% 12.25/1.94    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK3))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f60])).
% 12.25/1.94  fof(f60,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f25])).
% 12.25/1.94  fof(f1044,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1043,f128])).
% 12.25/1.94  fof(f1043,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1042,f122])).
% 12.25/1.94  fof(f122,plain,(
% 12.25/1.94    v1_pre_topc(k1_tsep_1(sK0,sK1,sK3))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f61])).
% 12.25/1.94  fof(f61,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f25])).
% 12.25/1.94  fof(f1042,plain,(
% 12.25/1.94    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(superposition,[],[f64,f110])).
% 12.25/1.94  fof(f110,plain,(
% 12.25/1.94    k1_tsep_1(sK0,sK1,sK3) = k1_tsep_1(sK0,sK3,sK1)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f44,f45,f59])).
% 12.25/1.94  fof(f59,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f23])).
% 12.25/1.94  fof(f23,plain,(
% 12.25/1.94    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(flattening,[],[f22])).
% 12.25/1.94  fof(f22,plain,(
% 12.25/1.94    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f3])).
% 12.25/1.94  fof(f3,axiom,(
% 12.25/1.94    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).
% 12.25/1.94  fof(f64,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(equality_resolution,[],[f54])).
% 12.25/1.94  fof(f54,plain,(
% 12.25/1.94    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f35])).
% 12.25/1.94  fof(f35,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(nnf_transformation,[],[f18])).
% 12.25/1.94  fof(f18,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(flattening,[],[f17])).
% 12.25/1.94  fof(f17,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f4])).
% 12.25/1.94  fof(f4,axiom,(
% 12.25/1.94    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 12.25/1.94  fof(f59058,plain,(
% 12.25/1.94    r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK1)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f58055,f58415,f63])).
% 12.25/1.94  fof(f63,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f27])).
% 12.25/1.94  fof(f27,plain,(
% 12.25/1.94    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 12.25/1.94    inference(flattening,[],[f26])).
% 12.25/1.94  fof(f26,plain,(
% 12.25/1.94    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 12.25/1.94    inference(ennf_transformation,[],[f2])).
% 12.25/1.94  fof(f2,axiom,(
% 12.25/1.94    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 12.25/1.94  fof(f58415,plain,(
% 12.25/1.94    r1_tarski(u1_struct_0(sK1),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f58031,f53266])).
% 12.25/1.94  fof(f53266,plain,(
% 12.25/1.94    ( ! [X3] : (~r1_tarski(u1_struct_0(sK2),X3) | r1_tarski(u1_struct_0(sK1),X3)) )),
% 12.25/1.94    inference(resolution,[],[f14387,f13983])).
% 12.25/1.94  fof(f13983,plain,(
% 12.25/1.94    ( ! [X3] : (~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),X3) | r1_tarski(u1_struct_0(sK1),X3)) )),
% 12.25/1.94    inference(superposition,[],[f58,f207])).
% 12.25/1.94  fof(f207,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 12.25/1.94    inference(subsumption_resolution,[],[f206,f37])).
% 12.25/1.94  fof(f206,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f205,f39])).
% 12.25/1.94  fof(f205,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f204,f40])).
% 12.25/1.94  fof(f204,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f203,f41])).
% 12.25/1.94  fof(f203,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f202,f42])).
% 12.25/1.94  fof(f202,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f201,f43])).
% 12.25/1.94  fof(f201,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f200,f93])).
% 12.25/1.94  fof(f93,plain,(
% 12.25/1.94    ~v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f42,f43,f60])).
% 12.25/1.94  fof(f200,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f199,f101])).
% 12.25/1.94  fof(f101,plain,(
% 12.25/1.94    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f42,f43,f62])).
% 12.25/1.94  fof(f199,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(resolution,[],[f97,f64])).
% 12.25/1.94  fof(f97,plain,(
% 12.25/1.94    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f40,f41,f42,f43,f61])).
% 12.25/1.94  fof(f58,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f21])).
% 12.25/1.94  fof(f21,plain,(
% 12.25/1.94    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 12.25/1.94    inference(ennf_transformation,[],[f1])).
% 12.25/1.94  fof(f1,axiom,(
% 12.25/1.94    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 12.25/1.94  fof(f14387,plain,(
% 12.25/1.94    ( ! [X2] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),X2) | ~r1_tarski(u1_struct_0(sK2),X2)) )),
% 12.25/1.94    inference(duplicate_literal_removal,[],[f14385])).
% 12.25/1.94  fof(f14385,plain,(
% 12.25/1.94    ( ! [X2] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)),X2) | ~r1_tarski(u1_struct_0(sK2),X2) | ~r1_tarski(u1_struct_0(sK2),X2)) )),
% 12.25/1.94    inference(superposition,[],[f63,f1153])).
% 12.25/1.94  fof(f1153,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2))),
% 12.25/1.94    inference(subsumption_resolution,[],[f1152,f37])).
% 12.25/1.94  fof(f1152,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1151,f39])).
% 12.25/1.94  fof(f1151,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1150,f42])).
% 12.25/1.94  fof(f1150,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1149,f43])).
% 12.25/1.94  fof(f1149,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1148,f93])).
% 12.25/1.94  fof(f1148,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1147,f101])).
% 12.25/1.94  fof(f1147,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1144,f97])).
% 12.25/1.94  fof(f1144,plain,(
% 12.25/1.94    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(duplicate_literal_removal,[],[f1143])).
% 12.25/1.94  fof(f1143,plain,(
% 12.25/1.94    ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(superposition,[],[f64,f181])).
% 12.25/1.94  fof(f181,plain,(
% 12.25/1.94    k1_tsep_1(sK0,sK2,sK2) = k1_tsep_1(sK0,sK1,sK2)),
% 12.25/1.94    inference(backward_demodulation,[],[f86,f179])).
% 12.25/1.94  fof(f179,plain,(
% 12.25/1.94    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK1,sK2)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f38,f39,f40,f42,f41,f43,f48,f52])).
% 12.25/1.94  fof(f52,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f34])).
% 12.25/1.94  fof(f34,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(nnf_transformation,[],[f16])).
% 12.25/1.94  fof(f16,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(flattening,[],[f15])).
% 12.25/1.94  fof(f15,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f6])).
% 12.25/1.94  fof(f6,axiom,(
% 12.25/1.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 12.25/1.94  fof(f48,plain,(
% 12.25/1.94    m1_pre_topc(sK1,sK2)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f86,plain,(
% 12.25/1.94    g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f38,f39,f42,f43,f51])).
% 12.25/1.94  fof(f51,plain,(
% 12.25/1.94    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f14])).
% 12.25/1.94  fof(f14,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 12.25/1.94    inference(flattening,[],[f13])).
% 12.25/1.94  fof(f13,plain,(
% 12.25/1.94    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 12.25/1.94    inference(ennf_transformation,[],[f7])).
% 12.25/1.94  fof(f7,axiom,(
% 12.25/1.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 12.25/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 12.25/1.94  fof(f58031,plain,(
% 12.25/1.94    r1_tarski(u1_struct_0(sK2),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f52252,f14014])).
% 12.25/1.94  fof(f14014,plain,(
% 12.25/1.94    ( ! [X3] : (~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),X3) | r1_tarski(u1_struct_0(sK2),X3)) )),
% 12.25/1.94    inference(superposition,[],[f58,f251])).
% 12.25/1.94  fof(f251,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))),
% 12.25/1.94    inference(subsumption_resolution,[],[f250,f37])).
% 12.25/1.94  fof(f250,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f249,f39])).
% 12.25/1.94  fof(f249,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f248,f42])).
% 12.25/1.94  fof(f248,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f247,f43])).
% 12.25/1.94  fof(f247,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f246,f46])).
% 12.25/1.94  fof(f246,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f245,f47])).
% 12.25/1.94  fof(f245,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f244,f151])).
% 12.25/1.94  fof(f151,plain,(
% 12.25/1.94    ~v2_struct_0(k1_tsep_1(sK0,sK2,sK4))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f60])).
% 12.25/1.94  fof(f244,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f243,f167])).
% 12.25/1.94  fof(f243,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) | u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(resolution,[],[f159,f64])).
% 12.25/1.94  fof(f159,plain,(
% 12.25/1.94    v1_pre_topc(k1_tsep_1(sK0,sK2,sK4))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f61])).
% 12.25/1.94  fof(f52252,plain,(
% 12.25/1.94    r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f167,f167,f52247,f68])).
% 12.25/1.94  fof(f68,plain,(
% 12.25/1.94    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X0,X1)) )),
% 12.25/1.94    inference(subsumption_resolution,[],[f65,f39])).
% 12.25/1.94  fof(f65,plain,(
% 12.25/1.94    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK0) | ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))) )),
% 12.25/1.94    inference(resolution,[],[f38,f57])).
% 12.25/1.94  fof(f57,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 12.25/1.94    inference(cnf_transformation,[],[f36])).
% 12.25/1.94  fof(f52247,plain,(
% 12.25/1.94    m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK2,sK4))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f38,f39,f151,f151,f167,f167,f763,f53])).
% 12.25/1.94  fof(f53,plain,(
% 12.25/1.94    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 12.25/1.94    inference(cnf_transformation,[],[f34])).
% 12.25/1.94  fof(f763,plain,(
% 12.25/1.94    g1_pre_topc(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),u1_pre_topc(k1_tsep_1(sK0,sK2,sK4))) = k1_tsep_1(sK0,k1_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK2,sK4))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f38,f39,f151,f167,f51])).
% 12.25/1.94  fof(f58055,plain,(
% 12.25/1.94    r1_tarski(u1_struct_0(sK3),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f58030,f53276])).
% 12.25/1.94  fof(f53276,plain,(
% 12.25/1.94    ( ! [X3] : (~r1_tarski(u1_struct_0(sK4),X3) | r1_tarski(u1_struct_0(sK3),X3)) )),
% 12.25/1.94    inference(resolution,[],[f14394,f14020])).
% 12.25/1.94  fof(f14020,plain,(
% 12.25/1.94    ( ! [X3] : (~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),X3) | r1_tarski(u1_struct_0(sK3),X3)) )),
% 12.25/1.94    inference(superposition,[],[f58,f260])).
% 12.25/1.94  fof(f260,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4))),
% 12.25/1.94    inference(subsumption_resolution,[],[f259,f37])).
% 12.25/1.94  fof(f259,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f258,f39])).
% 12.25/1.94  fof(f258,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f257,f44])).
% 12.25/1.94  fof(f257,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f256,f45])).
% 12.25/1.94  fof(f256,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f255,f46])).
% 12.25/1.94  fof(f255,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f254,f47])).
% 12.25/1.94  fof(f254,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f253,f152])).
% 12.25/1.94  fof(f152,plain,(
% 12.25/1.94    ~v2_struct_0(k1_tsep_1(sK0,sK3,sK4))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f44,f45,f46,f47,f60])).
% 12.25/1.94  fof(f253,plain,(
% 12.25/1.94    k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f252,f168])).
% 12.25/1.94  fof(f168,plain,(
% 12.25/1.94    m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f44,f45,f46,f47,f62])).
% 12.25/1.94  fof(f252,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) | k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) | v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(resolution,[],[f160,f64])).
% 12.25/1.94  fof(f160,plain,(
% 12.25/1.94    v1_pre_topc(k1_tsep_1(sK0,sK3,sK4))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f44,f45,f46,f47,f61])).
% 12.25/1.94  fof(f14394,plain,(
% 12.25/1.94    ( ! [X2] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),X2) | ~r1_tarski(u1_struct_0(sK4),X2)) )),
% 12.25/1.94    inference(duplicate_literal_removal,[],[f14392])).
% 12.25/1.94  fof(f14392,plain,(
% 12.25/1.94    ( ! [X2] : (r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK3,sK4)),X2) | ~r1_tarski(u1_struct_0(sK4),X2) | ~r1_tarski(u1_struct_0(sK4),X2)) )),
% 12.25/1.94    inference(superposition,[],[f63,f1166])).
% 12.25/1.94  fof(f1166,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4))),
% 12.25/1.94    inference(subsumption_resolution,[],[f1165,f37])).
% 12.25/1.94  fof(f1165,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1164,f39])).
% 12.25/1.94  fof(f1164,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1163,f46])).
% 12.25/1.94  fof(f1163,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1162,f47])).
% 12.25/1.94  fof(f1162,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1161,f152])).
% 12.25/1.94  fof(f1161,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1160,f168])).
% 12.25/1.94  fof(f1160,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) | u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1157,f160])).
% 12.25/1.94  fof(f1157,plain,(
% 12.25/1.94    ~v1_pre_topc(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) | u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(duplicate_literal_removal,[],[f1156])).
% 12.25/1.94  fof(f1156,plain,(
% 12.25/1.94    ~v1_pre_topc(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK3,sK4),sK0) | u1_struct_0(k1_tsep_1(sK0,sK3,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK4)) | v2_struct_0(k1_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(superposition,[],[f64,f187])).
% 12.25/1.94  fof(f187,plain,(
% 12.25/1.94    k1_tsep_1(sK0,sK4,sK4) = k1_tsep_1(sK0,sK3,sK4)),
% 12.25/1.94    inference(backward_demodulation,[],[f137,f185])).
% 12.25/1.94  fof(f185,plain,(
% 12.25/1.94    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK0,sK3,sK4)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f38,f39,f44,f46,f45,f47,f49,f52])).
% 12.25/1.94  fof(f49,plain,(
% 12.25/1.94    m1_pre_topc(sK3,sK4)),
% 12.25/1.94    inference(cnf_transformation,[],[f33])).
% 12.25/1.94  fof(f137,plain,(
% 12.25/1.94    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK0,sK4,sK4)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f38,f39,f46,f47,f51])).
% 12.25/1.94  fof(f58030,plain,(
% 12.25/1.94    r1_tarski(u1_struct_0(sK4),u1_struct_0(k1_tsep_1(sK0,sK2,sK4)))),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f52252,f14374])).
% 12.25/1.94  fof(f14374,plain,(
% 12.25/1.94    ( ! [X3] : (~r1_tarski(u1_struct_0(k1_tsep_1(sK0,sK2,sK4)),X3) | r1_tarski(u1_struct_0(sK4),X3)) )),
% 12.25/1.94    inference(superposition,[],[f58,f1110])).
% 12.25/1.94  fof(f1110,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2))),
% 12.25/1.94    inference(subsumption_resolution,[],[f1109,f37])).
% 12.25/1.94  fof(f1109,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1108,f39])).
% 12.25/1.94  fof(f1108,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1107,f46])).
% 12.25/1.94  fof(f1107,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1106,f47])).
% 12.25/1.94  fof(f1106,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1105,f42])).
% 12.25/1.94  fof(f1105,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1104,f43])).
% 12.25/1.94  fof(f1104,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1103,f151])).
% 12.25/1.94  fof(f1103,plain,(
% 12.25/1.94    u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1102,f167])).
% 12.25/1.94  fof(f1102,plain,(
% 12.25/1.94    ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) | u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(subsumption_resolution,[],[f1101,f159])).
% 12.25/1.94  fof(f1101,plain,(
% 12.25/1.94    ~v1_pre_topc(k1_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) | u1_struct_0(k1_tsep_1(sK0,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK4),u1_struct_0(sK2)) | v2_struct_0(k1_tsep_1(sK0,sK2,sK4)) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 12.25/1.94    inference(superposition,[],[f64,f143])).
% 12.25/1.94  fof(f143,plain,(
% 12.25/1.94    k1_tsep_1(sK0,sK2,sK4) = k1_tsep_1(sK0,sK4,sK2)),
% 12.25/1.94    inference(unit_resulting_resolution,[],[f37,f39,f42,f43,f46,f47,f59])).
% 12.25/1.94  % SZS output end Proof for theBenchmark
% 12.25/1.94  % (12303)------------------------------
% 12.25/1.94  % (12303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.25/1.94  % (12303)Termination reason: Refutation
% 12.25/1.94  
% 12.25/1.94  % (12303)Memory used [KB]: 35308
% 12.25/1.94  % (12303)Time elapsed: 1.478 s
% 12.25/1.94  % (12303)------------------------------
% 12.25/1.94  % (12303)------------------------------
% 12.25/1.94  % (12284)Success in time 1.582 s
%------------------------------------------------------------------------------
