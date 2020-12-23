%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1138+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 682 expanded)
%              Number of leaves         :   16 ( 271 expanded)
%              Depth                    :   21
%              Number of atoms          :  391 (4814 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f187,plain,(
    $false ),
    inference(subsumption_resolution,[],[f183,f186])).

fof(f186,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f172,f185])).

fof(f185,plain,(
    r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f68,f182])).

fof(f182,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f163,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f163,plain,(
    r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f155,f83])).

fof(f83,plain,(
    r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f82,f41])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    & r1_orders_2(sK0,sK2,sK3)
    & r1_orders_2(sK0,sK1,sK2)
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X1,X3)
                    & r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(sK0,X1,X3)
                  & r1_orders_2(sK0,X2,X3)
                  & r1_orders_2(sK0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_orders_2(sK0,X1,X3)
                & r1_orders_2(sK0,X2,X3)
                & r1_orders_2(sK0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_orders_2(sK0,sK1,X3)
              & r1_orders_2(sK0,X2,X3)
              & r1_orders_2(sK0,sK1,X2)
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ r1_orders_2(sK0,sK1,X3)
            & r1_orders_2(sK0,X2,X3)
            & r1_orders_2(sK0,sK1,X2)
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ~ r1_orders_2(sK0,sK1,X3)
          & r1_orders_2(sK0,sK2,X3)
          & r1_orders_2(sK0,sK1,sK2)
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ r1_orders_2(sK0,sK1,X3)
        & r1_orders_2(sK0,sK2,X3)
        & r1_orders_2(sK0,sK1,sK2)
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ~ r1_orders_2(sK0,sK1,sK3)
      & r1_orders_2(sK0,sK2,sK3)
      & r1_orders_2(sK0,sK1,sK2)
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_orders_2(X0,X1,X3)
                  & r1_orders_2(X0,X2,X3)
                  & r1_orders_2(X0,X1,X2)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).

fof(f82,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f81,f42])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f79,f43])).

fof(f43,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    r1_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f155,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_orders_2(sK0))
      | r2_hidden(sK2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f122,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f122,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
      | ~ r2_hidden(X0,u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f116,f96])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
      | ~ r2_hidden(X1,u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f74,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f74,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f55,f41])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f116,plain,
    ( v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | r2_hidden(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f108,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f108,plain,(
    m1_subset_1(k4_tarski(sK1,sK2),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    inference(resolution,[],[f95,f83])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_orders_2(sK0))
      | m1_subset_1(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f74,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f68,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f42])).

fof(f172,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f146,f163])).

fof(f146,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f145,f72])).

fof(f72,plain,(
    r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f71,plain,
    ( r8_relat_2(u1_orders_2(sK0),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f56,f40])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v4_orders_2(X0)
      | r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( ( v4_orders_2(X0)
          | ~ r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
        & ( r8_relat_2(u1_orders_2(X0),u1_struct_0(X0))
          | ~ v4_orders_2(X0) ) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v4_orders_2(X0)
      <=> r8_relat_2(u1_orders_2(X0),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_orders_2)).

fof(f145,plain,(
    ! [X0] :
      ( ~ r8_relat_2(u1_orders_2(sK0),X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f144,f41])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ r8_relat_2(u1_orders_2(sK0),X0)
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f143,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ r8_relat_2(u1_orders_2(sK0),X0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f44])).

fof(f44,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ r8_relat_2(u1_orders_2(sK0),X0)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(subsumption_resolution,[],[f138,f47])).

fof(f47,plain,(
    ~ r1_orders_2(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f138,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ r8_relat_2(u1_orders_2(sK0),X0)
      | r1_orders_2(sK0,sK1,sK3)
      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f111,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f111,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1,sK3),u1_orders_2(sK0))
      | ~ r2_hidden(sK3,X0)
      | ~ r2_hidden(sK2,X0)
      | ~ r2_hidden(sK1,X0)
      | ~ r8_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f98,f83])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK0))
      | ~ r2_hidden(sK3,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r8_relat_2(u1_orders_2(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f92,f94])).

fof(f94,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK3),u1_orders_2(sK0))
      | ~ r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0))
      | ~ r2_hidden(sK3,X1)
      | ~ r2_hidden(sK2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ r8_relat_2(u1_orders_2(sK0),X1)
      | ~ v1_relat_1(u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X6,X0,X7,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X6,X7),X0)
      | r2_hidden(k4_tarski(X5,X7),X0)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ r8_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
              & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
              & r2_hidden(sK6(X0,X1),X1)
              & r2_hidden(sK5(X0,X1),X1)
              & r2_hidden(sK4(X0,X1),X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2,X3,X4] :
          ( ~ r2_hidden(k4_tarski(X2,X4),X0)
          & r2_hidden(k4_tarski(X3,X4),X0)
          & r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X4,X1)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X0)
        & r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)
        & r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

% (4950)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% (4963)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% (4955)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% (4962)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% (4953)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% (4961)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% (4968)lrs+10_4_add=off:afp=100000:afq=2.0:amm=sco:anc=none:nm=64:nwc=1:stl=150:sp=occurrence:updr=off_733 on theBenchmark
% (4969)dis+1_14_awrs=converge:awrsf=256:av=off:bs=on:bsr=on:bce=on:cond=fast:gsp=input_only:gs=on:lcm=predicate:lma=on:nm=4:nwc=1.7:sp=weighted_frequency:urr=on_33 on theBenchmark
% (4951)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X5,X6,X7] :
                ( r2_hidden(k4_tarski(X5,X7),X0)
                | ~ r2_hidden(k4_tarski(X6,X7),X0)
                | ~ r2_hidden(k4_tarski(X5,X6),X0)
                | ~ r2_hidden(X7,X1)
                | ~ r2_hidden(X6,X1)
                | ~ r2_hidden(X5,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r8_relat_2(X0,X1)
            | ? [X2,X3,X4] :
                ( ~ r2_hidden(k4_tarski(X2,X4),X0)
                & r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3,X4] :
                ( r2_hidden(k4_tarski(X2,X4),X0)
                | ~ r2_hidden(k4_tarski(X3,X4),X0)
                | ~ r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r8_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

% (4966)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( r2_hidden(k4_tarski(X2,X4),X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r8_relat_2(X0,X1)
        <=> ! [X2,X3,X4] :
              ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X4,X1)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) )
             => r2_hidden(k4_tarski(X2,X4),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_relat_2)).

fof(f86,plain,(
    r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0)) ),
    inference(subsumption_resolution,[],[f85,f41])).

fof(f85,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f80,f44])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK2,sK3),u1_orders_2(sK0))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f58,f46])).

fof(f46,plain,(
    r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f183,plain,(
    r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f70,f182])).

fof(f70,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f60,f44])).

%------------------------------------------------------------------------------
