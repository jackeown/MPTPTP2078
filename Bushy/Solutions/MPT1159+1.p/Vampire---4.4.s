%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t57_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:22 EDT 2019

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 797 expanded)
%              Number of leaves         :   40 ( 317 expanded)
%              Depth                    :   19
%              Number of atoms          :  675 (8221 expanded)
%              Number of equality atoms :   35 ( 127 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9623,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f182,f186,f230,f254,f264,f266,f293,f315,f318,f321,f346,f982,f2086,f2240,f2259,f6927,f7178,f8111,f8146,f9622])).

fof(f9622,plain,
    ( ~ spl11_5
    | ~ spl11_827
    | spl11_1
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f9614,f200,f167,f9620,f173])).

fof(f173,plain,
    ( spl11_5
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f9620,plain,
    ( spl11_827
  <=> ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_827])])).

fof(f167,plain,
    ( spl11_1
  <=> ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f200,plain,
    ( spl11_10
  <=> k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f9614,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ r2_hidden(sK1,sK3)
    | ~ spl11_1
    | ~ spl11_10 ),
    inference(resolution,[],[f664,f168])).

fof(f168,plain,
    ( ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f167])).

fof(f664,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k3_orders_2(sK0,sK3,sK2))
        | ~ r2_hidden(X2,k2_orders_2(sK0,k1_tarski(sK2)))
        | ~ r2_hidden(X2,sK3) )
    | ~ spl11_10 ),
    inference(superposition,[],[f163,f626])).

fof(f626,plain,
    ( k3_orders_2(sK0,sK3,sK2) = k3_xboole_0(sK3,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f623,f201])).

fof(f201,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f200])).

fof(f623,plain,(
    k3_orders_2(sK0,sK3,sK2) = k3_xboole_0(sK3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f621,f112])).

fof(f112,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,
    ( ( ~ r2_hidden(sK1,sK3)
      | ~ r2_orders_2(sK0,sK1,sK2)
      | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r2_orders_2(sK0,sK1,sK2) )
      | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f80,f84,f83,f82,f81])).

fof(f81,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2)
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(sK0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(sK0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(sK0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(sK0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(X0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ r2_hidden(sK1,X3)
                  | ~ r2_orders_2(X0,sK1,X2)
                  | ~ r2_hidden(sK1,k3_orders_2(X0,X3,X2)) )
                & ( ( r2_hidden(sK1,X3)
                    & r2_orders_2(X0,sK1,X2) )
                  | r2_hidden(sK1,k3_orders_2(X0,X3,X2)) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ r2_hidden(X1,X3)
                | ~ r2_orders_2(X0,X1,X2)
                | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
              & ( ( r2_hidden(X1,X3)
                  & r2_orders_2(X0,X1,X2) )
                | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ( ~ r2_hidden(X1,X3)
              | ~ r2_orders_2(X0,X1,sK2)
              | ~ r2_hidden(X1,k3_orders_2(X0,X3,sK2)) )
            & ( ( r2_hidden(X1,X3)
                & r2_orders_2(X0,X1,sK2) )
              | r2_hidden(X1,k3_orders_2(X0,X3,sK2)) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X1,X3)
            | ~ r2_orders_2(X0,X1,X2)
            | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
          & ( ( r2_hidden(X1,X3)
              & r2_orders_2(X0,X1,X2) )
            | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ r2_hidden(X1,sK3)
          | ~ r2_orders_2(X0,X1,X2)
          | ~ r2_hidden(X1,k3_orders_2(X0,sK3,X2)) )
        & ( ( r2_hidden(X1,sK3)
            & r2_orders_2(X0,X1,X2) )
          | r2_hidden(X1,k3_orders_2(X0,sK3,X2)) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(X0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f79])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r2_hidden(X1,X3)
                    | ~ r2_orders_2(X0,X1,X2)
                    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & ( ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) )
                    | r2_hidden(X1,k3_orders_2(X0,X3,X2)) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <~> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <~> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t57_orders_2)).

fof(f621,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_orders_2(sK0,sK3,X0) = k3_xboole_0(sK3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0))) ) ),
    inference(forward_demodulation,[],[f620,f127])).

fof(f127,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',commutativity_k3_xboole_0)).

fof(f620,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f238,f235])).

fof(f235,plain,(
    ! [X4] : k3_xboole_0(X4,sK3) = k9_subset_1(u1_struct_0(sK0),X4,sK3) ),
    inference(resolution,[],[f113,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',redefinition_k9_subset_1)).

fof(f113,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f85])).

fof(f238,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3) ) ),
    inference(global_subsumption,[],[f106,f108,f109,f110,f107,f231])).

fof(f231,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f113,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',d14_orders_2)).

fof(f107,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f110,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f109,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f108,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f106,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f163,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f153])).

fof(f153,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(sK8(X0,X1,X2),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK8(X0,X1,X2),X1)
              & r2_hidden(sK8(X0,X1,X2),X0) )
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f99,f100])).

fof(f100,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(sK8(X0,X1,X2),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(sK8(X0,X1,X2),X0) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f98])).

fof(f98,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f97])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',d4_xboole_0)).

fof(f8146,plain,
    ( spl11_12
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_19
    | ~ spl11_21
    | ~ spl11_23
    | ~ spl11_25
    | spl11_826
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f8142,f200,f184,f8144,f223,f220,f217,f214,f211,f208,f205])).

fof(f205,plain,
    ( spl11_12
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f208,plain,
    ( spl11_15
  <=> ~ v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_15])])).

fof(f211,plain,
    ( spl11_17
  <=> ~ v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f214,plain,
    ( spl11_19
  <=> ~ v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f217,plain,
    ( spl11_21
  <=> ~ l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f220,plain,
    ( spl11_23
  <=> ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_23])])).

fof(f223,plain,
    ( spl11_25
  <=> ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_25])])).

fof(f8144,plain,
    ( spl11_826
  <=> r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_826])])).

fof(f184,plain,
    ( spl11_2
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f8142,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2
    | ~ spl11_10 ),
    inference(forward_demodulation,[],[f8141,f201])).

fof(f8141,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_2 ),
    inference(resolution,[],[f185,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X2)
      | r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
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
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t52_orders_2)).

fof(f185,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f184])).

fof(f8111,plain,
    ( ~ spl11_0
    | ~ spl11_208 ),
    inference(avatar_contradiction_clause,[],[f8084])).

fof(f8084,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_208 ),
    inference(subsumption_resolution,[],[f178,f1278])).

fof(f1278,plain,
    ( ! [X2] : ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK2))
    | ~ spl11_208 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1277,plain,
    ( spl11_208
  <=> ! [X2] : ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_208])])).

fof(f178,plain,
    ( r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2))
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl11_0
  <=> r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f7178,plain,
    ( ~ spl11_115
    | spl11_208
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f4357,f200,f1277,f1274])).

fof(f1274,plain,
    ( spl11_115
  <=> ~ v1_xboole_0(k2_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_115])])).

fof(f4357,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k3_orders_2(sK0,sK3,sK2))
        | ~ v1_xboole_0(k2_orders_2(sK0,k1_tarski(sK2))) )
    | ~ spl11_10 ),
    inference(resolution,[],[f663,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t7_boole)).

fof(f663,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k2_orders_2(sK0,k1_tarski(sK2)))
        | ~ r2_hidden(X1,k3_orders_2(sK0,sK3,sK2)) )
    | ~ spl11_10 ),
    inference(superposition,[],[f164,f626])).

fof(f164,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f152])).

fof(f152,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f6927,plain,
    ( spl11_2
    | ~ spl11_23
    | ~ spl11_0
    | ~ spl11_10
    | ~ spl11_116 ),
    inference(avatar_split_clause,[],[f6925,f712,f200,f177,f220,f184])).

fof(f712,plain,
    ( spl11_116
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k2_orders_2(sK0,k1_tarski(sK2)))
        | r2_orders_2(sK0,X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_116])])).

fof(f6925,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r2_orders_2(sK0,sK1,sK2)
    | ~ spl11_0
    | ~ spl11_10
    | ~ spl11_116 ),
    inference(resolution,[],[f6864,f713])).

fof(f713,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k2_orders_2(sK0,k1_tarski(sK2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_orders_2(sK0,X3,sK2) )
    | ~ spl11_116 ),
    inference(avatar_component_clause,[],[f712])).

fof(f6864,plain,
    ( m1_subset_1(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl11_0
    | ~ spl11_10 ),
    inference(resolution,[],[f1262,f178])).

fof(f1262,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_orders_2(sK0,sK3,sK2))
        | m1_subset_1(X3,k2_orders_2(sK0,k1_tarski(sK2))) )
    | ~ spl11_10 ),
    inference(resolution,[],[f663,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t1_subset)).

fof(f2259,plain,
    ( spl11_114
    | spl11_116
    | ~ spl11_76 ),
    inference(avatar_split_clause,[],[f2253,f442,f712,f709])).

fof(f709,plain,
    ( spl11_114
  <=> v1_xboole_0(k2_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_114])])).

fof(f442,plain,
    ( spl11_76
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k1_tarski(sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_76])])).

fof(f2253,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_orders_2(sK0,X3,sK2)
        | v1_xboole_0(k2_orders_2(sK0,k1_tarski(sK2)))
        | ~ m1_subset_1(X3,k2_orders_2(sK0,k1_tarski(sK2))) )
    | ~ spl11_76 ),
    inference(resolution,[],[f443,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',t2_subset)).

fof(f443,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k1_tarski(sK2)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK2) )
    | ~ spl11_76 ),
    inference(avatar_component_clause,[],[f442])).

fof(f2240,plain,
    ( spl11_12
    | ~ spl11_15
    | ~ spl11_17
    | ~ spl11_19
    | ~ spl11_21
    | ~ spl11_25
    | spl11_76
    | ~ spl11_10 ),
    inference(avatar_split_clause,[],[f2238,f200,f442,f223,f217,f214,f211,f208,f205])).

fof(f2238,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_orders_2(sK0,k1_tarski(sK2)))
        | r2_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_10 ),
    inference(superposition,[],[f122,f201])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f2086,plain,
    ( spl11_6
    | spl11_10 ),
    inference(avatar_split_clause,[],[f2085,f200,f192])).

fof(f192,plain,
    ( spl11_6
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f2085,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f112,f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',redefinition_k6_domain_1)).

fof(f982,plain,
    ( ~ spl11_0
    | spl11_5
    | ~ spl11_10 ),
    inference(avatar_contradiction_clause,[],[f977])).

fof(f977,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_5
    | ~ spl11_10 ),
    inference(subsumption_resolution,[],[f174,f941])).

fof(f941,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl11_0
    | ~ spl11_10 ),
    inference(resolution,[],[f662,f178])).

fof(f662,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,sK3,sK2))
        | r2_hidden(X0,sK3) )
    | ~ spl11_10 ),
    inference(superposition,[],[f165,f626])).

fof(f165,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f151])).

fof(f151,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f101])).

fof(f174,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f346,plain,(
    ~ spl11_12 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl11_12 ),
    inference(subsumption_resolution,[],[f106,f206])).

fof(f206,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f205])).

fof(f321,plain,(
    spl11_25 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | ~ spl11_25 ),
    inference(subsumption_resolution,[],[f112,f224])).

fof(f224,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl11_25 ),
    inference(avatar_component_clause,[],[f223])).

fof(f318,plain,(
    spl11_47 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl11_47 ),
    inference(subsumption_resolution,[],[f110,f294])).

fof(f294,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_47 ),
    inference(resolution,[],[f292,f119])).

fof(f119,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',dt_l1_orders_2)).

fof(f292,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_47 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl11_47
  <=> ~ l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_47])])).

fof(f315,plain,(
    spl11_23 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl11_23 ),
    inference(subsumption_resolution,[],[f111,f221])).

fof(f221,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl11_23 ),
    inference(avatar_component_clause,[],[f220])).

fof(f111,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f85])).

fof(f293,plain,
    ( spl11_12
    | ~ spl11_47
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f287,f192,f291,f205])).

fof(f287,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_6 ),
    inference(resolution,[],[f193,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t57_orders_2.p',fc2_struct_0)).

fof(f193,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f192])).

fof(f266,plain,(
    spl11_21 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f110,f218])).

fof(f218,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f217])).

fof(f264,plain,(
    spl11_19 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl11_19 ),
    inference(subsumption_resolution,[],[f109,f215])).

fof(f215,plain,
    ( ~ v5_orders_2(sK0)
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f214])).

fof(f254,plain,(
    spl11_17 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f108,f212])).

fof(f212,plain,
    ( ~ v4_orders_2(sK0)
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f211])).

fof(f230,plain,(
    spl11_15 ),
    inference(avatar_contradiction_clause,[],[f229])).

fof(f229,plain,
    ( $false
    | ~ spl11_15 ),
    inference(subsumption_resolution,[],[f107,f209])).

fof(f209,plain,
    ( ~ v3_orders_2(sK0)
    | ~ spl11_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f186,plain,
    ( spl11_0
    | spl11_2 ),
    inference(avatar_split_clause,[],[f114,f184,f177])).

fof(f114,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f85])).

fof(f182,plain,
    ( spl11_0
    | spl11_4 ),
    inference(avatar_split_clause,[],[f115,f180,f177])).

fof(f180,plain,
    ( spl11_4
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f115,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f85])).

fof(f175,plain,
    ( ~ spl11_1
    | ~ spl11_3
    | ~ spl11_5 ),
    inference(avatar_split_clause,[],[f116,f173,f170,f167])).

fof(f170,plain,
    ( spl11_3
  <=> ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f116,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_orders_2(sK0,sK1,sK2)
    | ~ r2_hidden(sK1,k3_orders_2(sK0,sK3,sK2)) ),
    inference(cnf_transformation,[],[f85])).
%------------------------------------------------------------------------------
