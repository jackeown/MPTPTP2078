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
% DateTime   : Thu Dec  3 13:10:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  114 (1322 expanded)
%              Number of leaves         :    6 ( 410 expanded)
%              Depth                    :   32
%              Number of atoms          :  690 (13041 expanded)
%              Number of equality atoms :  131 (2935 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f538,plain,(
    $false ),
    inference(subsumption_resolution,[],[f488,f475])).

fof(f475,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f450,f258])).

fof(f258,plain,
    ( r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f181,f75])).

fof(f75,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f74,f19])).

fof(f19,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( ( k1_xboole_0 = sK1
        & ~ m1_orders_2(sK1,sK0,sK1) )
      | ( m1_orders_2(sK1,sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
              | ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,sK0,X1) )
            | ( m1_orders_2(X1,sK0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ( ( k1_xboole_0 = X1
            & ~ m1_orders_2(X1,sK0,X1) )
          | ( m1_orders_2(X1,sK0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ( k1_xboole_0 = sK1
          & ~ m1_orders_2(sK1,sK0,sK1) )
        | ( m1_orders_2(sK1,sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f74,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f73,f20])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f72,f21])).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f47,f22])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0) ),
    inference(resolution,[],[f18,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_orders_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
                        & r2_hidden(sK2(X0,X1,X2),X1)
                        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f181,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f180,f40])).

fof(f40,plain,
    ( k1_xboole_0 != sK1
    | ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f24])).

fof(f24,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).

fof(f180,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f179,f18])).

fof(f179,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f178,f19])).

fof(f178,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f177,f20])).

fof(f177,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f176,f21])).

fof(f176,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f175,f22])).

fof(f175,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f166,f23])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f166,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f160,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f159])).

fof(f159,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_orders_2(sK1,sK0,sK1) ),
    inference(superposition,[],[f40,f27])).

fof(f27,plain,
    ( k1_xboole_0 = sK1
    | m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f450,plain,(
    ~ r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    inference(forward_demodulation,[],[f444,f439])).

fof(f439,plain,(
    sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f438,f382])).

fof(f382,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f188,f75])).

fof(f188,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    inference(subsumption_resolution,[],[f187,f40])).

fof(f187,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f186,f18])).

fof(f186,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f185,f19])).

fof(f185,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f184,f20])).

fof(f184,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f183,f21])).

fof(f183,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f182,f22])).

fof(f182,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f165,f23])).

fof(f165,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f438,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    inference(duplicate_literal_removal,[],[f422])).

fof(f422,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f23,f226])).

fof(f226,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f225,f18])).

fof(f225,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f224,f19])).

fof(f224,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f223,f20])).

fof(f223,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f222,f21])).

fof(f222,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f221,f22])).

fof(f221,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f206,f23])).

fof(f206,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f158,f31])).

fof(f158,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f23,f27])).

fof(f444,plain,(
    ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) ),
    inference(resolution,[],[f421,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k3_orders_2(sK0,sK1,X0)) ) ),
    inference(subsumption_resolution,[],[f116,f18])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f115,f19])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f114,f20])).

% (14714)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f114,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f113,f21])).

fof(f113,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f104,f22])).

fof(f104,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_orders_2(sK0,sK1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).

fof(f421,plain,(
    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f420,f293])).

fof(f293,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f174,f75])).

fof(f174,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f173,f40])).

fof(f173,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f172,f18])).

fof(f172,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f171,f19])).

fof(f171,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f170,f20])).

fof(f170,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f169,f21])).

fof(f169,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f168,f22])).

fof(f168,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f167,f23])).

fof(f167,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f161])).

fof(f161,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f160,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f420,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f404])).

fof(f404,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f23,f214])).

fof(f214,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f213,f18])).

fof(f213,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f19])).

fof(f212,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f20])).

fof(f211,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f21])).

fof(f210,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f209,f22])).

fof(f209,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f208,f23])).

fof(f208,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f202])).

fof(f202,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f158,f29])).

fof(f488,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f23,f487])).

fof(f487,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f486,f27])).

fof(f486,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f485,f18])).

fof(f485,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f484,f19])).

fof(f484,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f483,f20])).

fof(f483,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f482,f21])).

fof(f482,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f481,f22])).

fof(f481,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f480,f23])).

fof(f480,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f476])).

fof(f476,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f450,f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (14711)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.47  % (14719)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (14713)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (14723)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (14707)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (14707)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (14721)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.49  % (14723)Refutation not found, incomplete strategy% (14723)------------------------------
% 0.22/0.49  % (14723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14723)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (14723)Memory used [KB]: 10618
% 0.22/0.49  % (14723)Time elapsed: 0.070 s
% 0.22/0.49  % (14723)------------------------------
% 0.22/0.49  % (14723)------------------------------
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f538,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f488,f475])).
% 0.22/0.49  fof(f475,plain,(
% 0.22/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(resolution,[],[f450,f258])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(resolution,[],[f181,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    (((k1_xboole_0 = sK1 & ~m1_orders_2(sK1,sK0,sK1)) | (m1_orders_2(sK1,sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK0,X1)) | (m1_orders_2(X1,sK0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK0,X1)) | (m1_orders_2(X1,sK0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (((k1_xboole_0 = sK1 & ~m1_orders_2(sK1,sK0,sK1)) | (m1_orders_2(sK1,sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f5])).
% 0.22/0.49  fof(f5,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f3])).
% 0.22/0.49  fof(f3,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f73,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f72,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f47,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0)),
% 0.22/0.49    inference(resolution,[],[f18,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0] : (m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_orders_2(k1_xboole_0,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(rectify,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f181,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f180,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    k1_xboole_0 != sK1 | ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.49    inference(inner_rewriting,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f180,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1),
% 0.22/0.49    inference(subsumption_resolution,[],[f179,f18])).
% 0.22/0.49  fof(f179,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f178,f19])).
% 0.22/0.49  fof(f178,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f177,f20])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f176,f21])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f175,f22])).
% 0.22/0.49  fof(f175,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f166,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f162])).
% 0.22/0.49  fof(f162,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | r2_hidden(sK2(sK0,sK1,sK1),sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f160,f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f160,plain,(
% 0.22/0.49    m1_orders_2(sK1,sK0,sK1) | ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.49    inference(trivial_inequality_removal,[],[f159])).
% 0.22/0.49  fof(f159,plain,(
% 0.22/0.49    k1_xboole_0 != k1_xboole_0 | ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_orders_2(sK1,sK0,sK1)),
% 0.22/0.49    inference(superposition,[],[f40,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | m1_orders_2(sK1,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f450,plain,(
% 0.22/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f444,f439])).
% 0.22/0.49  fof(f439,plain,(
% 0.22/0.49    sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f438,f382])).
% 0.22/0.49  fof(f382,plain,(
% 0.22/0.49    sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(resolution,[],[f188,f75])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f187,f40])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1),
% 0.22/0.49    inference(subsumption_resolution,[],[f186,f18])).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f185,f19])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f184,f20])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f183,f21])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f182,f22])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f165,f23])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f163])).
% 0.22/0.49  fof(f163,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f160,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f438,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f422])).
% 0.22/0.49  fof(f422,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(superposition,[],[f23,f226])).
% 0.22/0.49  fof(f226,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f225,f18])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f224,f19])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f223,f20])).
% 0.22/0.49  fof(f223,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f222,f21])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f221,f22])).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f206,f23])).
% 0.22/0.49  fof(f206,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f204])).
% 0.22/0.49  fof(f204,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f158,f31])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    m1_orders_2(sK1,sK0,sK1) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(superposition,[],[f23,f27])).
% 0.22/0.49  fof(f444,plain,(
% 0.22/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))),
% 0.22/0.49    inference(resolution,[],[f421,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,sK1,X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f116,f18])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f19])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f114,f20])).
% 0.22/0.49  % (14714)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f113,f21])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f104,f22])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k3_orders_2(sK0,sK1,X0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.49    inference(resolution,[],[f23,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).
% 0.22/0.49  fof(f421,plain,(
% 0.22/0.49    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f420,f293])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(resolution,[],[f174,f75])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(subsumption_resolution,[],[f173,f40])).
% 0.22/0.49  fof(f173,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1),
% 0.22/0.49    inference(subsumption_resolution,[],[f172,f18])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f171,f19])).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f170,f20])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f169,f21])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f168,f22])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f167,f23])).
% 0.22/0.49  fof(f167,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f161])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f160,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f420,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f404])).
% 0.22/0.49  fof(f404,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(superposition,[],[f23,f214])).
% 0.22/0.49  fof(f214,plain,(
% 0.22/0.49    k1_xboole_0 = sK1 | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f213,f18])).
% 0.22/0.49  fof(f213,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f212,f19])).
% 0.22/0.49  fof(f212,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f211,f20])).
% 0.22/0.49  fof(f211,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f210,f21])).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f209,f22])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f208,f23])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f202])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f158,f29])).
% 0.22/0.49  fof(f488,plain,(
% 0.22/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(backward_demodulation,[],[f23,f487])).
% 0.22/0.49  fof(f487,plain,(
% 0.22/0.49    k1_xboole_0 = sK1),
% 0.22/0.49    inference(subsumption_resolution,[],[f486,f27])).
% 0.22/0.49  fof(f486,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1),
% 0.22/0.49    inference(subsumption_resolution,[],[f485,f18])).
% 0.22/0.49  fof(f485,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f484,f19])).
% 0.22/0.49  fof(f484,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f483,f20])).
% 0.22/0.49  fof(f483,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f482,f21])).
% 0.22/0.49  fof(f482,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f481,f22])).
% 0.22/0.49  fof(f481,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f480,f23])).
% 0.22/0.49  fof(f480,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f476])).
% 0.22/0.49  fof(f476,plain,(
% 0.22/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.49    inference(resolution,[],[f450,f30])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (14707)------------------------------
% 0.22/0.49  % (14707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (14707)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (14707)Memory used [KB]: 1791
% 0.22/0.49  % (14707)Time elapsed: 0.068 s
% 0.22/0.49  % (14707)------------------------------
% 0.22/0.49  % (14707)------------------------------
% 0.22/0.49  % (14702)Success in time 0.132 s
%------------------------------------------------------------------------------
