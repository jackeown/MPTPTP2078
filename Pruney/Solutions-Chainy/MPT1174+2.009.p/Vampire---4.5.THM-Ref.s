%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 501 expanded)
%              Number of leaves         :   14 ( 198 expanded)
%              Depth                    :   33
%              Number of atoms          :  737 (4315 expanded)
%              Number of equality atoms :   70 ( 976 expanded)
%              Maximal formula depth    :   18 (   9 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f46])).

fof(f46,plain,(
    m2_orders_2(sK3,sK0,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
    & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
    & m2_orders_2(sK3,sK0,sK2)
    & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                    & k1_funct_1(X2,u1_struct_0(X0)) = X1
                    & m2_orders_2(X3,X0,X2) )
                & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(sK0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(sK0)) = X1
                  & m2_orders_2(X3,sK0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( k1_xboole_0 != k3_orders_2(sK0,X3,X1)
                & k1_funct_1(X2,u1_struct_0(sK0)) = X1
                & m2_orders_2(X3,sK0,X2) )
            & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
              & k1_funct_1(X2,u1_struct_0(sK0)) = sK1
              & m2_orders_2(X3,sK0,X2) )
          & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
            & k1_funct_1(X2,u1_struct_0(sK0)) = sK1
            & m2_orders_2(X3,sK0,X2) )
        & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
          & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
          & m2_orders_2(X3,sK0,sK2) )
      & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( k1_xboole_0 != k3_orders_2(sK0,X3,sK1)
        & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
        & m2_orders_2(X3,sK0,sK2) )
   => ( k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)
      & sK1 = k1_funct_1(sK2,u1_struct_0(sK0))
      & m2_orders_2(sK3,sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).

fof(f139,plain,(
    ~ m2_orders_2(sK3,sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m2_orders_2(sK3,sK0,sK2) ),
    inference(superposition,[],[f48,f125])).

% (27159)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f125,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m2_orders_2(X1,sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f124,f70])).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X0,sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f69,f39])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f68,f40])).

fof(f40,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f67,f41])).

fof(f41,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f66,f42])).

fof(f42,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f65,f43])).

fof(f43,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK2)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f124,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f123,f39])).

fof(f123,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f40])).

fof(f122,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f121,f41])).

fof(f121,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f43])).

fof(f119,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f44])).

fof(f44,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f117,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X1] :
      ( ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) ) ),
    inference(resolution,[],[f113,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(X0,X1,X2)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f75,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(k3_orders_2(X1,X0,X2)),u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_xboole_0 = k3_orders_2(X1,X0,X2) ) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK4(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK4(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_orders_2(X1,X2,X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f58,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_orders_2(X0,X1,X2)),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK4(k3_orders_2(X0,X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,X1,X2) ) ),
    inference(resolution,[],[f51,f54])).

% (27146)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f112,f44])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f111,f39])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f110,f40])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f109,f41])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f108,f42])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f107,f43])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | k1_xboole_0 = k3_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f106,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X1,X0,sK4(k3_orders_2(X1,X2,X0)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f87,f74])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r3_orders_2(X1,X0,sK4(k3_orders_2(X1,X2,X0)))
      | ~ m1_subset_1(sK4(k3_orders_2(X1,X2,X0)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r3_orders_2(X1,X0,sK4(k3_orders_2(X1,X2,X0)))
      | ~ m1_subset_1(sK4(k3_orders_2(X1,X2,X0)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f85,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,X2,sK4(k3_orders_2(X1,X0,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f84,f74])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X2,sK4(k3_orders_2(X1,X0,X2)))
      | ~ m1_subset_1(sK4(k3_orders_2(X1,X0,X2)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | k1_xboole_0 = k3_orders_2(X1,X0,X2)
      | ~ r1_orders_2(X1,X2,sK4(k3_orders_2(X1,X0,X2)))
      | ~ m1_subset_1(sK4(k3_orders_2(X1,X0,X2)),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f81,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,sK4(k3_orders_2(X0,X1,X2)),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f79,f74])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,sK4(k3_orders_2(X0,X1,X2)),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK4(k3_orders_2(X0,X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = k3_orders_2(X0,X1,X2) ) ),
    inference(resolution,[],[f50,f54])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f105,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X0,sK0,sK2)
      | m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f70,f61])).

fof(f105,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f104,f39])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f103,f40])).

fof(f103,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f102,f41])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f101,f42])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f100,f43])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r3_orders_2(sK0,sK1,X0)
      | ~ r2_hidden(X0,X1)
      | ~ m2_orders_2(X1,sK0,sK2)
      | ~ m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f62,f47])).

fof(f47,plain,(
    sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X2,X1)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).

fof(f48,plain,(
    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:40:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.42  % (27156)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.42  % (27154)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.43  % (27147)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.44  % (27147)Refutation not found, incomplete strategy% (27147)------------------------------
% 0.19/0.44  % (27147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.44  % (27165)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.44  % (27147)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.44  
% 0.19/0.44  % (27147)Memory used [KB]: 10618
% 0.19/0.44  % (27147)Time elapsed: 0.067 s
% 0.19/0.44  % (27147)------------------------------
% 0.19/0.44  % (27147)------------------------------
% 0.19/0.45  % (27155)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.45  % (27157)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.45  % (27164)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.45  % (27162)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.45  % (27150)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.46  % (27165)Refutation found. Thanks to Tanya!
% 0.19/0.46  % SZS status Theorem for theBenchmark
% 0.19/0.46  % SZS output start Proof for theBenchmark
% 0.19/0.46  fof(f140,plain,(
% 0.19/0.46    $false),
% 0.19/0.46    inference(subsumption_resolution,[],[f139,f46])).
% 0.19/0.46  fof(f46,plain,(
% 0.19/0.46    m2_orders_2(sK3,sK0,sK2)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f33,plain,(
% 0.19/0.46    (((k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(sK3,sK0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f13,f32,f31,f30,f29])).
% 0.19/0.46  fof(f29,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,X1) & k1_funct_1(X2,u1_struct_0(sK0)) = X1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f30,plain,(
% 0.19/0.46    ? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,X1) & k1_funct_1(X2,u1_struct_0(sK0)) = X1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & k1_funct_1(X2,u1_struct_0(sK0)) = sK1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f31,plain,(
% 0.19/0.46    ? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & k1_funct_1(X2,u1_struct_0(sK0)) = sK1 & m2_orders_2(X3,sK0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(X3,sK0,sK2)) & m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f32,plain,(
% 0.19/0.46    ? [X3] : (k1_xboole_0 != k3_orders_2(sK0,X3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(X3,sK0,sK2)) => (k1_xboole_0 != k3_orders_2(sK0,sK3,sK1) & sK1 = k1_funct_1(sK2,u1_struct_0(sK0)) & m2_orders_2(sK3,sK0,sK2))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f13,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f12])).
% 0.19/0.46  fof(f12,plain,(
% 0.19/0.46    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f10])).
% 0.19/0.46  fof(f10,negated_conjecture,(
% 0.19/0.46    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.19/0.46    inference(negated_conjecture,[],[f9])).
% 0.19/0.46  fof(f9,conjecture,(
% 0.19/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_orders_2)).
% 0.19/0.46  fof(f139,plain,(
% 0.19/0.46    ~m2_orders_2(sK3,sK0,sK2)),
% 0.19/0.46    inference(trivial_inequality_removal,[],[f127])).
% 0.19/0.46  fof(f127,plain,(
% 0.19/0.46    k1_xboole_0 != k1_xboole_0 | ~m2_orders_2(sK3,sK0,sK2)),
% 0.19/0.46    inference(superposition,[],[f48,f125])).
% 0.19/0.46  % (27159)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  fof(f125,plain,(
% 0.19/0.46    ( ! [X1] : (k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m2_orders_2(X1,sK0,sK2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f124,f70])).
% 0.19/0.46  fof(f70,plain,(
% 0.19/0.46    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,sK2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f69,f39])).
% 0.19/0.46  fof(f39,plain,(
% 0.19/0.46    ~v2_struct_0(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f69,plain,(
% 0.19/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f68,f40])).
% 0.19/0.46  fof(f40,plain,(
% 0.19/0.46    v3_orders_2(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f68,plain,(
% 0.19/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f67,f41])).
% 0.19/0.46  fof(f41,plain,(
% 0.19/0.46    v4_orders_2(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f67,plain,(
% 0.19/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f66,f42])).
% 0.19/0.46  fof(f42,plain,(
% 0.19/0.46    v5_orders_2(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f66,plain,(
% 0.19/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f65,f43])).
% 0.19/0.46  fof(f43,plain,(
% 0.19/0.46    l1_orders_2(sK0)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f65,plain,(
% 0.19/0.46    ( ! [X0] : (~m2_orders_2(X0,sK0,sK2) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(resolution,[],[f57,f45])).
% 0.19/0.46  fof(f45,plain,(
% 0.19/0.46    m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0)))),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f57,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f22])).
% 0.19/0.46  fof(f22,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f21])).
% 0.19/0.46  fof(f21,plain,(
% 0.19/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f11])).
% 0.19/0.46  fof(f11,plain,(
% 0.19/0.46    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.46    inference(pure_predicate_removal,[],[f4])).
% 0.19/0.46  fof(f4,axiom,(
% 0.19/0.46    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.19/0.46  fof(f124,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f123,f39])).
% 0.19/0.46  fof(f123,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f122,f40])).
% 0.19/0.46  fof(f122,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f121,f41])).
% 0.19/0.46  fof(f121,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f120,f42])).
% 0.19/0.46  fof(f120,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f119,f43])).
% 0.19/0.46  fof(f119,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f117,f44])).
% 0.19/0.46  fof(f44,plain,(
% 0.19/0.46    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f117,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f115])).
% 0.19/0.46  fof(f115,plain,(
% 0.19/0.46    ( ! [X1] : (~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X1,sK1)) )),
% 0.19/0.46    inference(resolution,[],[f113,f76])).
% 0.19/0.46  fof(f76,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_orders_2(X0,X1,X2)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,X1,X2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f75,f74])).
% 0.19/0.46  fof(f74,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (m1_subset_1(sK4(k3_orders_2(X1,X0,X2)),u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X1)) | k1_xboole_0 = k3_orders_2(X1,X0,X2)) )),
% 0.19/0.46    inference(resolution,[],[f71,f54])).
% 0.19/0.46  fof(f54,plain,(
% 0.19/0.46    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.19/0.46    inference(cnf_transformation,[],[f37])).
% 0.19/0.46  fof(f37,plain,(
% 0.19/0.46    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)) | k1_xboole_0 = X0)),
% 0.19/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f36])).
% 0.19/0.46  fof(f36,plain,(
% 0.19/0.46    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK4(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK4(X0),X0)))),
% 0.19/0.46    introduced(choice_axiom,[])).
% 0.19/0.46  fof(f20,plain,(
% 0.19/0.46    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.19/0.46    inference(ennf_transformation,[],[f2])).
% 0.19/0.46  fof(f2,axiom,(
% 0.19/0.46    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 0.19/0.46  fof(f71,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k3_orders_2(X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.46    inference(resolution,[],[f58,f61])).
% 0.19/0.46  fof(f61,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f28])).
% 0.19/0.46  fof(f28,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.19/0.46    inference(flattening,[],[f27])).
% 0.19/0.46  fof(f27,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.19/0.46    inference(ennf_transformation,[],[f1])).
% 0.19/0.46  fof(f1,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.19/0.46  fof(f58,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f24])).
% 0.19/0.46  fof(f24,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f23])).
% 0.19/0.46  fof(f23,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f3])).
% 0.19/0.46  fof(f3,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_orders_2)).
% 0.19/0.46  fof(f75,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_orders_2(X0,X1,X2)),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(sK4(k3_orders_2(X0,X1,X2)),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,X1,X2)) )),
% 0.19/0.46    inference(resolution,[],[f51,f54])).
% 0.19/0.46  % (27146)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.46  fof(f51,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f35])).
% 0.19/0.46  fof(f35,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f34])).
% 0.19/0.46  fof(f34,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f17])).
% 0.19/0.46  fof(f17,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f16])).
% 0.19/0.46  fof(f16,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f7])).
% 0.19/0.46  fof(f7,axiom,(
% 0.19/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.19/0.46  fof(f113,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f112,f44])).
% 0.19/0.46  fof(f112,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f111,f39])).
% 0.19/0.46  fof(f111,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f110,f40])).
% 0.19/0.46  fof(f110,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f109,f41])).
% 0.19/0.46  fof(f109,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f108,f42])).
% 0.19/0.46  fof(f108,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f107,f43])).
% 0.19/0.46  fof(f107,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~r2_hidden(sK4(k3_orders_2(sK0,X0,sK1)),X1) | ~m2_orders_2(X1,sK0,sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = k3_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(resolution,[],[f106,f88])).
% 0.19/0.46  fof(f88,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r3_orders_2(X1,X0,sK4(k3_orders_2(X1,X2,X0))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f87,f74])).
% 0.19/0.46  fof(f87,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r3_orders_2(X1,X0,sK4(k3_orders_2(X1,X2,X0))) | ~m1_subset_1(sK4(k3_orders_2(X1,X2,X0)),u1_struct_0(X1))) )),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f86])).
% 0.19/0.46  fof(f86,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r3_orders_2(X1,X0,sK4(k3_orders_2(X1,X2,X0))) | ~m1_subset_1(sK4(k3_orders_2(X1,X2,X0)),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.19/0.46    inference(resolution,[],[f85,f59])).
% 0.19/0.46  fof(f59,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f38])).
% 0.19/0.46  fof(f38,plain,(
% 0.19/0.46    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(nnf_transformation,[],[f26])).
% 0.19/0.46  fof(f26,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f25])).
% 0.19/0.46  fof(f25,plain,(
% 0.19/0.46    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f5])).
% 0.19/0.46  fof(f5,axiom,(
% 0.19/0.46    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.19/0.46  fof(f85,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r1_orders_2(X1,X2,sK4(k3_orders_2(X1,X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f84,f74])).
% 0.19/0.46  fof(f84,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X2,sK4(k3_orders_2(X1,X0,X2))) | ~m1_subset_1(sK4(k3_orders_2(X1,X0,X2)),u1_struct_0(X1))) )),
% 0.19/0.46    inference(duplicate_literal_removal,[],[f83])).
% 0.19/0.46  fof(f83,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | k1_xboole_0 = k3_orders_2(X1,X0,X2) | ~r1_orders_2(X1,X2,sK4(k3_orders_2(X1,X0,X2))) | ~m1_subset_1(sK4(k3_orders_2(X1,X0,X2)),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1)) )),
% 0.19/0.46    inference(resolution,[],[f81,f53])).
% 0.19/0.46  fof(f53,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f19])).
% 0.19/0.46  fof(f19,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.19/0.46    inference(flattening,[],[f18])).
% 0.19/0.46  fof(f18,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f6])).
% 0.19/0.46  fof(f6,axiom,(
% 0.19/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).
% 0.19/0.46  fof(f81,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_orders_2(X0,sK4(k3_orders_2(X0,X1,X2)),X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,X1,X2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f79,f74])).
% 0.19/0.46  fof(f79,plain,(
% 0.19/0.46    ( ! [X2,X0,X1] : (r2_orders_2(X0,sK4(k3_orders_2(X0,X1,X2)),X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(sK4(k3_orders_2(X0,X1,X2)),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = k3_orders_2(X0,X1,X2)) )),
% 0.19/0.46    inference(resolution,[],[f50,f54])).
% 0.19/0.46  fof(f50,plain,(
% 0.19/0.46    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | r2_orders_2(X0,X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f35])).
% 0.19/0.46  fof(f106,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f105,f72])).
% 0.19/0.46  fof(f72,plain,(
% 0.19/0.46    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK2) | m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0)) )),
% 0.19/0.46    inference(resolution,[],[f70,f61])).
% 0.19/0.46  fof(f105,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f104,f39])).
% 0.19/0.46  fof(f104,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f103,f40])).
% 0.19/0.46  fof(f103,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f102,f41])).
% 0.19/0.46  fof(f102,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f101,f42])).
% 0.19/0.46  fof(f101,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f100,f43])).
% 0.19/0.46  fof(f100,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f99,f44])).
% 0.19/0.46  fof(f99,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(subsumption_resolution,[],[f96,f45])).
% 0.19/0.46  fof(f96,plain,(
% 0.19/0.46    ( ! [X0,X1] : (r3_orders_2(sK0,sK1,X0) | ~r2_hidden(X0,X1) | ~m2_orders_2(X1,sK0,sK2) | ~m1_orders_1(sK2,k1_orders_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.46    inference(superposition,[],[f62,f47])).
% 0.19/0.46  fof(f47,plain,(
% 0.19/0.46    sK1 = k1_funct_1(sK2,u1_struct_0(sK0))),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  fof(f62,plain,(
% 0.19/0.46    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(equality_resolution,[],[f49])).
% 0.19/0.46  fof(f49,plain,(
% 0.19/0.46    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.19/0.46    inference(cnf_transformation,[],[f15])).
% 0.19/0.46  fof(f15,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.46    inference(flattening,[],[f14])).
% 0.19/0.46  fof(f14,plain,(
% 0.19/0.46    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.46    inference(ennf_transformation,[],[f8])).
% 0.19/0.46  fof(f8,axiom,(
% 0.19/0.46    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 0.19/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_orders_2)).
% 0.19/0.46  fof(f48,plain,(
% 0.19/0.46    k1_xboole_0 != k3_orders_2(sK0,sK3,sK1)),
% 0.19/0.46    inference(cnf_transformation,[],[f33])).
% 0.19/0.46  % SZS output end Proof for theBenchmark
% 0.19/0.46  % (27165)------------------------------
% 0.19/0.46  % (27165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (27165)Termination reason: Refutation
% 0.19/0.46  
% 0.19/0.46  % (27165)Memory used [KB]: 1663
% 0.19/0.46  % (27165)Time elapsed: 0.086 s
% 0.19/0.46  % (27165)------------------------------
% 0.19/0.46  % (27165)------------------------------
% 0.19/0.46  % (27148)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.46  % (27146)Refutation not found, incomplete strategy% (27146)------------------------------
% 0.19/0.46  % (27146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (27146)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (27146)Memory used [KB]: 6140
% 0.19/0.46  % (27146)Time elapsed: 0.071 s
% 0.19/0.46  % (27146)------------------------------
% 0.19/0.46  % (27146)------------------------------
% 0.19/0.47  % (27144)Success in time 0.128 s
%------------------------------------------------------------------------------
