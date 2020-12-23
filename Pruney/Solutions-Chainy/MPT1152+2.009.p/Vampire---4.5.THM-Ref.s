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
% DateTime   : Thu Dec  3 13:09:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 (7925 expanded)
%              Number of leaves         :   19 (2082 expanded)
%              Depth                    :   35
%              Number of atoms          :  480 (39313 expanded)
%              Number of equality atoms :   60 (6710 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f324,plain,(
    $false ),
    inference(subsumption_resolution,[],[f320,f293])).

fof(f293,plain,(
    ~ m1_subset_1(k2_orders_2(sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f218,f223])).

fof(f223,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(backward_demodulation,[],[f183,f189])).

fof(f189,plain,(
    k1_xboole_0 = k2_struct_0(sK2) ),
    inference(resolution,[],[f184,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f184,plain,(
    ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK2)) ),
    inference(resolution,[],[f183,f83])).

fof(f83,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f55,f54])).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f183,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f182,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f182,plain,(
    v1_xboole_0(k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f181,f162])).

fof(f162,plain,(
    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f161,f158])).

fof(f158,plain,(
    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(resolution,[],[f152,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK5(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK4(X0,X1,X3))
              & r2_hidden(sK4(X0,X1,X3),X1)
              & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK5(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK5(X0,X1,X2) = X2
          & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).

fof(f45,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK4(X0,X1,X3))
        & r2_hidden(sK4(X0,X1,X3),X1)
        & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK5(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK5(X0,X1,X2) = X2
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X3,X4)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f152,plain,(
    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f151,f53])).

fof(f53,plain,(
    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f35])).

fof(f35,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).

fof(f151,plain,
    ( k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2))
    | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) ),
    inference(forward_demodulation,[],[f147,f140])).

fof(f140,plain,(
    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f139,f83])).

fof(f139,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(forward_demodulation,[],[f138,f85])).

fof(f85,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f57,f52])).

fof(f52,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f137,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f137,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f49,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f135,f50])).

fof(f50,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f134,f52])).

fof(f134,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f61,f51])).

fof(f51,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f147,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(backward_demodulation,[],[f130,f140])).

fof(f130,plain,
    ( sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2))))
    | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2)) ),
    inference(resolution,[],[f129,f62])).

fof(f129,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK2,k2_struct_0(sK2)))
      | sP0(sK2,k2_struct_0(sK2),X1) ) ),
    inference(resolution,[],[f123,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f123,plain,(
    ! [X0] : sP1(X0,k2_struct_0(sK2),sK2) ),
    inference(resolution,[],[f122,f83])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(forward_demodulation,[],[f121,f85])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f120,f48])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f119,f49])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f118,f50])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f117,f52])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | sP1(X1,X0,sK2)
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | sP1(X0,X2,X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f28,f33,f32])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f161,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f157,f85])).

fof(f157,plain,(
    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2)) ),
    inference(resolution,[],[f152,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f181,plain,
    ( v1_xboole_0(k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(resolution,[],[f178,f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f178,plain,(
    ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f177,f162])).

fof(f177,plain,
    ( ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) ),
    inference(forward_demodulation,[],[f176,f85])).

fof(f176,plain,
    ( ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f174,f52])).

fof(f174,plain,
    ( ~ r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))
    | ~ m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(resolution,[],[f163,f82])).

fof(f82,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(f163,plain,(
    ! [X0] :
      ( r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X0)
      | ~ r2_hidden(X0,k2_struct_0(sK2)) ) ),
    inference(backward_demodulation,[],[f160,f158])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(subsumption_resolution,[],[f159,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f76,f83])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f159,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK2))
      | ~ r2_hidden(X0,k2_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(forward_demodulation,[],[f156,f85])).

fof(f156,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0) ) ),
    inference(resolution,[],[f152,f71])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | r2_orders_2(X0,sK5(X0,X1,X2),X6) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f218,plain,(
    r2_hidden(sK3(k2_orders_2(sK2,k1_xboole_0)),k2_orders_2(sK2,k1_xboole_0)) ),
    inference(backward_demodulation,[],[f165,f189])).

fof(f165,plain,(
    r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_orders_2(sK2,k2_struct_0(sK2))) ),
    inference(resolution,[],[f145,f152])).

fof(f145,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k2_struct_0(sK2),X0)
      | r2_hidden(X0,k2_orders_2(sK2,k2_struct_0(sK2))) ) ),
    inference(backward_demodulation,[],[f128,f140])).

fof(f128,plain,(
    ! [X0] :
      ( ~ sP0(sK2,k2_struct_0(sK2),X0)
      | r2_hidden(X0,a_2_1_orders_2(sK2,k2_struct_0(sK2))) ) ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f320,plain,(
    m1_subset_1(k2_orders_2(sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f276,f83])).

fof(f276,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f275,f194])).

fof(f194,plain,(
    k1_xboole_0 = u1_struct_0(sK2) ),
    inference(backward_demodulation,[],[f85,f189])).

fof(f275,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(forward_demodulation,[],[f274,f194])).

fof(f274,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f273,f48])).

fof(f273,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f272,f49])).

fof(f272,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f271,f50])).

fof(f271,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f270,f52])).

fof(f270,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ l1_orders_2(sK2)
      | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
      | ~ v4_orders_2(sK2)
      | ~ v3_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.48  % (1263)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.48  % (1257)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.48  % (1250)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.49  % (1255)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (1252)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (1274)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (1253)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.49  % (1265)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (1266)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (1250)Refutation not found, incomplete strategy% (1250)------------------------------
% 0.21/0.49  % (1250)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1250)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (1250)Memory used [KB]: 10618
% 0.21/0.49  % (1250)Time elapsed: 0.086 s
% 0.21/0.49  % (1250)------------------------------
% 0.21/0.49  % (1250)------------------------------
% 0.21/0.50  % (1256)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (1257)Refutation not found, incomplete strategy% (1257)------------------------------
% 0.21/0.50  % (1257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1257)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1257)Memory used [KB]: 10618
% 0.21/0.50  % (1257)Time elapsed: 0.097 s
% 0.21/0.50  % (1257)------------------------------
% 0.21/0.50  % (1257)------------------------------
% 0.21/0.50  % (1256)Refutation not found, incomplete strategy% (1256)------------------------------
% 0.21/0.50  % (1256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1256)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1256)Memory used [KB]: 6140
% 0.21/0.50  % (1256)Time elapsed: 0.097 s
% 0.21/0.50  % (1256)------------------------------
% 0.21/0.50  % (1256)------------------------------
% 0.21/0.50  % (1261)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (1253)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f324,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f320,f293])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    ~m1_subset_1(k2_orders_2(sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    inference(resolution,[],[f218,f223])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f183,f189])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    k1_xboole_0 = k2_struct_0(sK2)),
% 0.21/0.50    inference(resolution,[],[f184,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f22,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2))) )),
% 0.21/0.50    inference(resolution,[],[f183,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f55,f54])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | ~r2_hidden(X1,X0)) )),
% 0.21/0.50    inference(resolution,[],[f182,f77])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.50  fof(f182,plain,(
% 0.21/0.50    v1_xboole_0(k2_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f181,f162])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f161,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    sK3(k2_orders_2(sK2,k2_struct_0(sK2))) = sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(resolution,[],[f152,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK5(X0,X1,X2) = X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK4(X0,X1,X3)) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f44,f46,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK4(X0,X1,X3)) & r2_hidden(sK4(X0,X1,X3),X1) & m1_subset_1(sK4(X0,X1,X3),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK5(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK5(X0,X1,X2) = X2 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.50    inference(rectify,[],[f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.21/0.50    inference(nnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (k1_xboole_0 != k2_orders_2(sK2,k2_struct_0(sK2)) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0] : (k1_xboole_0 != k2_orders_2(X0,k2_struct_0(X0)) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f13])).
% 0.21/0.50  fof(f13,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => k1_xboole_0 = k2_orders_2(X0,k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_orders_2)).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    k1_xboole_0 = k2_orders_2(sK2,k2_struct_0(sK2)) | sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2))))),
% 0.21/0.50    inference(forward_demodulation,[],[f147,f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    k2_orders_2(sK2,k2_struct_0(sK2)) = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f139,f83])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f138,f85])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.21/0.50    inference(resolution,[],[f56,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    l1_struct_0(sK2)),
% 0.21/0.50    inference(resolution,[],[f57,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    l1_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_struct_0(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f136,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    v3_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f135,f50])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v4_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f52])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | k2_orders_2(sK2,X0) = a_2_1_orders_2(sK2,X0) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f61,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v5_orders_2(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    sP0(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(backward_demodulation,[],[f130,f140])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    sP0(sK2,k2_struct_0(sK2),sK3(a_2_1_orders_2(sK2,k2_struct_0(sK2)))) | k1_xboole_0 = a_2_1_orders_2(sK2,k2_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f129,f62])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK2,k2_struct_0(sK2))) | sP0(sK2,k2_struct_0(sK2),X1)) )),
% 0.21/0.50    inference(resolution,[],[f123,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.50    inference(rectify,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.50    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ( ! [X0] : (sP1(X0,k2_struct_0(sK2),sK2)) )),
% 0.21/0.50    inference(resolution,[],[f122,f83])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f121,f85])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f48])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f119,f49])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f118,f50])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f117,f52])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | sP1(X1,X0,sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f75,f51])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v5_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | sP1(X0,X2,X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.50    inference(definition_folding,[],[f28,f33,f32])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.50  fof(f161,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),k2_struct_0(sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f157,f85])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    m1_subset_1(sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),u1_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f152,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f181,plain,(
% 0.21/0.50    v1_xboole_0(k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.50    inference(resolution,[],[f178,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f177,f162])).
% 0.21/0.50  fof(f177,plain,(
% 0.21/0.50    ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2))),
% 0.21/0.50    inference(forward_demodulation,[],[f176,f85])).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2))),
% 0.21/0.50    inference(subsumption_resolution,[],[f174,f52])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ~r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_struct_0(sK2)) | ~m1_subset_1(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),u1_struct_0(sK2)) | ~l1_orders_2(sK2)),
% 0.21/0.50    inference(resolution,[],[f163,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f78])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f59])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(nnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    ( ! [X0] : (r2_orders_2(sK2,sK3(k2_orders_2(sK2,k2_struct_0(sK2))),X0) | ~r2_hidden(X0,k2_struct_0(sK2))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f160,f158])).
% 0.21/0.50  fof(f160,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f159,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.21/0.50    inference(resolution,[],[f76,f83])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK2)) | ~r2_hidden(X0,k2_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f156,f85])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | r2_orders_2(sK2,sK5(sK2,k2_struct_0(sK2),sK3(k2_orders_2(sK2,k2_struct_0(sK2)))),X0)) )),
% 0.21/0.50    inference(resolution,[],[f152,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X6,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | r2_orders_2(X0,sK5(X0,X1,X2),X6)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f47])).
% 0.21/0.50  fof(f218,plain,(
% 0.21/0.50    r2_hidden(sK3(k2_orders_2(sK2,k1_xboole_0)),k2_orders_2(sK2,k1_xboole_0))),
% 0.21/0.50    inference(backward_demodulation,[],[f165,f189])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    r2_hidden(sK3(k2_orders_2(sK2,k2_struct_0(sK2))),k2_orders_2(sK2,k2_struct_0(sK2)))),
% 0.21/0.50    inference(resolution,[],[f145,f152])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    ( ! [X0] : (~sP0(sK2,k2_struct_0(sK2),X0) | r2_hidden(X0,k2_orders_2(sK2,k2_struct_0(sK2)))) )),
% 0.21/0.50    inference(backward_demodulation,[],[f128,f140])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    ( ! [X0] : (~sP0(sK2,k2_struct_0(sK2),X0) | r2_hidden(X0,a_2_1_orders_2(sK2,k2_struct_0(sK2)))) )),
% 0.21/0.50    inference(resolution,[],[f123,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_hidden(X0,a_2_1_orders_2(X2,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f42])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    m1_subset_1(k2_orders_2(sK2,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.50    inference(resolution,[],[f276,f83])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f275,f194])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    k1_xboole_0 = u1_struct_0(sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f85,f189])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f274,f194])).
% 0.21/0.50  fof(f274,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f273,f48])).
% 0.21/0.50  fof(f273,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f272,f49])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f271,f50])).
% 0.21/0.50  fof(f271,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f270,f52])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_orders_2(sK2) | m1_subset_1(k2_orders_2(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) )),
% 0.21/0.50    inference(resolution,[],[f66,f51])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v5_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (1253)------------------------------
% 0.21/0.50  % (1253)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1253)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (1253)Memory used [KB]: 6396
% 0.21/0.50  % (1253)Time elapsed: 0.096 s
% 0.21/0.50  % (1253)------------------------------
% 0.21/0.50  % (1253)------------------------------
% 0.21/0.50  % (1247)Success in time 0.144 s
%------------------------------------------------------------------------------
