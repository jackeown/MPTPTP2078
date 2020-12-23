%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t65_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:23 EDT 2019

% Result     : Theorem 193.64s
% Output     : Refutation 193.74s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 360 expanded)
%              Number of leaves         :   12 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :  361 (2944 expanded)
%              Number of equality atoms :   39 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98302,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f112,f492,f491,f98301])).

fof(f98301,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k3_orders_2(sK0,sK2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | r2_hidden(X2,k3_orders_2(sK0,sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f12215,f2860])).

fof(f2860,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_orders_2(sK0,sK2,X0))
      | r2_hidden(X1,sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f510,f2201])).

fof(f2201,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k3_xboole_0(sK2,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f2200,f125])).

fof(f125,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t65_orders_2.p',commutativity_k3_xboole_0)).

fof(f2200,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f382,f371])).

fof(f371,plain,(
    ! [X11] : k3_xboole_0(X11,sK2) = k9_subset_1(u1_struct_0(sK0),X11,sK2) ),
    inference(resolution,[],[f113,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t65_orders_2.p',redefinition_k9_subset_1)).

fof(f113,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,
    ( ~ r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1))
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f81,f80,f79,f78])).

fof(f78,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                    & r1_tarski(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(sK0,X2,X1),k3_orders_2(sK0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ r1_tarski(k3_orders_2(X0,X2,sK1),k3_orders_2(X0,X3,sK1))
                & r1_tarski(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
              & r1_tarski(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ r1_tarski(k3_orders_2(X0,sK2,X1),k3_orders_2(X0,X3,X1))
            & r1_tarski(sK2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
          & r1_tarski(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,sK3,X1))
        & r1_tarski(X2,sK3)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
                  ( ~ r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1))
                  & r1_tarski(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( r1_tarski(X2,X3)
                     => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r1_tarski(X2,X3)
                   => r1_tarski(k3_orders_2(X0,X2,X1),k3_orders_2(X0,X3,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t65_orders_2.p',t65_orders_2)).

fof(f382,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f381,f107])).

fof(f107,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f381,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f380,f108])).

fof(f108,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f380,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f379,f109])).

fof(f109,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f379,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f378,f110])).

fof(f110,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f378,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f359,f111])).

fof(f111,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f359,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK2,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f113,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t65_orders_2.p',d14_orders_2)).

fof(f510,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,k3_xboole_0(sK2,X5))
      | r2_hidden(X4,sK3) ) ),
    inference(resolution,[],[f315,f168])).

fof(f168,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f100,f101])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
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
    inference(rectify,[],[f99])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f98])).

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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t65_orders_2.p',d4_xboole_0)).

fof(f315,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f115,f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f89,f90])).

fof(f90,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t65_orders_2.p',d3_tarski)).

fof(f115,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

fof(f12215,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k3_orders_2(sK0,sK3,X3))
      | ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,sK2,X3)) ) ),
    inference(duplicate_literal_removal,[],[f12185])).

fof(f12185,plain,(
    ! [X2,X3] :
      ( r2_hidden(X2,k3_orders_2(sK0,sK3,X3))
      | ~ r2_hidden(X2,sK3)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r2_hidden(X2,k3_orders_2(sK0,sK2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f2268,f2212])).

fof(f2212,plain,(
    ! [X12,X11] :
      ( r2_hidden(X12,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X11)))
      | ~ r2_hidden(X12,k3_orders_2(sK0,sK2,X11))
      | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f167,f2201])).

fof(f167,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f155])).

fof(f155,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f102])).

fof(f2268,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X10,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X9)))
      | r2_hidden(X10,k3_orders_2(sK0,sK3,X9))
      | ~ r2_hidden(X10,sK3)
      | ~ m1_subset_1(X9,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f166,f2258])).

fof(f2258,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k3_xboole_0(sK3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f2257,f125])).

fof(f2257,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k3_xboole_0(k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f449,f438])).

fof(f438,plain,(
    ! [X11] : k3_xboole_0(X11,sK3) = k9_subset_1(u1_struct_0(sK0),X11,sK3) ),
    inference(resolution,[],[f114,f143])).

fof(f114,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f82])).

fof(f449,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f448,f107])).

fof(f448,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f447,f108])).

fof(f447,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f446,f109])).

fof(f446,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f445,f110])).

fof(f445,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f426,f111])).

fof(f426,plain,(
    ! [X0] :
      ( k3_orders_2(sK0,sK3,X0) = k9_subset_1(u1_struct_0(sK0),k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)),sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f114,f121])).

fof(f166,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f102])).

fof(f491,plain,(
    r2_hidden(sK6(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK2,sK1)) ),
    inference(resolution,[],[f116,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f116,plain,(
    ~ r1_tarski(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)) ),
    inference(cnf_transformation,[],[f82])).

fof(f492,plain,(
    ~ r2_hidden(sK6(k3_orders_2(sK0,sK2,sK1),k3_orders_2(sK0,sK3,sK1)),k3_orders_2(sK0,sK3,sK1)) ),
    inference(resolution,[],[f116,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f112,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
