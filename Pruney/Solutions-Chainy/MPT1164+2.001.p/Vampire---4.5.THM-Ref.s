%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 (1249 expanded)
%              Number of leaves         :   17 ( 466 expanded)
%              Depth                    :   32
%              Number of atoms          :  593 (8543 expanded)
%              Number of equality atoms :   59 ( 191 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f515,plain,(
    $false ),
    inference(subsumption_resolution,[],[f512,f85])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f512,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f382,f481])).

fof(f481,plain,(
    k1_xboole_0 = sK7 ),
    inference(subsumption_resolution,[],[f480,f381])).

fof(f381,plain,(
    m1_orders_2(sK7,sK5,k1_xboole_0) ),
    inference(backward_demodulation,[],[f55,f369])).

fof(f369,plain,(
    k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f368,f56])).

fof(f56,plain,(
    ~ r1_tarski(sK7,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(sK7,sK6)
    & m1_orders_2(sK7,sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & l1_orders_2(sK5)
    & v5_orders_2(sK5)
    & v4_orders_2(sK5)
    & v3_orders_2(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f10,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X2,X1)
                & m1_orders_2(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,sK5,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
      & l1_orders_2(sK5)
      & v5_orders_2(sK5)
      & v4_orders_2(sK5)
      & v3_orders_2(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(X2,X1)
            & m1_orders_2(X2,sK5,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) )
   => ( ? [X2] :
          ( ~ r1_tarski(X2,sK6)
          & m1_orders_2(X2,sK5,sK6) )
      & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(X2,sK6)
        & m1_orders_2(X2,sK5,sK6) )
   => ( ~ r1_tarski(sK7,sK6)
      & m1_orders_2(sK7,sK5,sK6) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f368,plain,
    ( k1_xboole_0 = sK6
    | r1_tarski(sK7,sK6) ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,
    ( k1_xboole_0 = sK6
    | r1_tarski(sK7,sK6)
    | r1_tarski(sK7,sK6) ),
    inference(resolution,[],[f290,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK9(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f290,plain,(
    ! [X0] :
      ( r2_hidden(sK9(sK7,X0),sK6)
      | k1_xboole_0 = sK6
      | r1_tarski(sK7,X0) ) ),
    inference(resolution,[],[f287,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f287,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK7)
      | r2_hidden(X2,sK6)
      | k1_xboole_0 = sK6 ) ),
    inference(subsumption_resolution,[],[f286,f183])).

fof(f183,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK5))
      | ~ r2_hidden(X0,sK7) ) ),
    inference(resolution,[],[f144,f55])).

fof(f144,plain,(
    ! [X10,X11] :
      ( ~ m1_orders_2(X10,sK5,sK6)
      | m1_subset_1(X11,u1_struct_0(sK5))
      | ~ r2_hidden(X11,X10) ) ),
    inference(resolution,[],[f126,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f126,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ m1_orders_2(X0,sK5,sK6) ) ),
    inference(subsumption_resolution,[],[f125,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f125,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f50,plain,(
    v3_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f124,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f51,plain,(
    v4_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f122,f52])).

fof(f52,plain,(
    v5_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f122,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f121,f53])).

fof(f53,plain,(
    l1_orders_2(sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ l1_orders_2(sK5)
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f73,f54])).

fof(f54,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).

fof(f286,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK7)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | r2_hidden(X2,sK6)
      | k1_xboole_0 = sK6 ) ),
    inference(resolution,[],[f231,f251])).

fof(f251,plain,
    ( sP2(sK7,sK6,sK5)
    | k1_xboole_0 = sK6 ),
    inference(subsumption_resolution,[],[f250,f55])).

fof(f250,plain,
    ( k1_xboole_0 = sK6
    | ~ m1_orders_2(sK7,sK5,sK6)
    | sP2(sK7,sK6,sK5) ),
    inference(resolution,[],[f240,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ m1_orders_2(X2,X0,X1)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_orders_2(X2,X0,X1)
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ m1_orders_2(X2,X0,X1) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_orders_2(X2,X0,X1)
      <=> sP2(X2,X1,X0) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f240,plain,
    ( sP3(sK5,sK6,sK7)
    | k1_xboole_0 = sK6 ),
    inference(resolution,[],[f217,f55])).

fof(f217,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | sP3(sK5,sK6,X0)
      | k1_xboole_0 = sK6 ) ),
    inference(resolution,[],[f154,f54])).

fof(f154,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))
      | k1_xboole_0 = X5
      | sP3(sK5,X5,X4)
      | ~ m1_orders_2(X4,sK5,sK6) ) ),
    inference(subsumption_resolution,[],[f153,f49])).

fof(f153,plain,(
    ! [X4,X5] :
      ( ~ m1_orders_2(X4,sK5,sK6)
      | k1_xboole_0 = X5
      | sP3(sK5,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f152,f50])).

fof(f152,plain,(
    ! [X4,X5] :
      ( ~ m1_orders_2(X4,sK5,sK6)
      | k1_xboole_0 = X5
      | sP3(sK5,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f151,f51])).

fof(f151,plain,(
    ! [X4,X5] :
      ( ~ m1_orders_2(X4,sK5,sK6)
      | k1_xboole_0 = X5
      | sP3(sK5,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f150,f52])).

fof(f150,plain,(
    ! [X4,X5] :
      ( ~ m1_orders_2(X4,sK5,sK6)
      | k1_xboole_0 = X5
      | sP3(sK5,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f141,f53])).

fof(f141,plain,(
    ! [X4,X5] :
      ( ~ m1_orders_2(X4,sK5,sK6)
      | k1_xboole_0 = X5
      | sP3(sK5,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ l1_orders_2(sK5)
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f126,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | sP3(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( sP4(X2,X1,X0)
                & ( sP3(X0,X1,X2)
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f25,f24,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ? [X3] :
          ( k3_orders_2(X0,X1,X3) = X2
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ( m1_orders_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ sP2(X3,sK6,sK5)
      | ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK5))
      | r2_hidden(X2,sK6) ) ),
    inference(resolution,[],[f173,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ~ r2_hidden(X1,X0)
        | ~ r2_orders_2(X3,X1,X2) )
      & ( ( r2_hidden(X1,X0)
          & r2_orders_2(X3,X1,X2) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X3,X1,X2,X0] :
      ( ( sP0(X3,X1,X2,X0)
        | ~ r2_hidden(X1,X3)
        | ~ r2_orders_2(X0,X1,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2) )
        | ~ sP0(X3,X1,X2,X0) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X3,X1,X2,X0] :
      ( ( sP0(X3,X1,X2,X0)
        | ~ r2_hidden(X1,X3)
        | ~ r2_orders_2(X0,X1,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_orders_2(X0,X1,X2) )
        | ~ sP0(X3,X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X3,X1,X2,X0] :
      ( sP0(X3,X1,X2,X0)
    <=> ( r2_hidden(X1,X3)
        & r2_orders_2(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f173,plain,(
    ! [X0,X1] :
      ( sP0(sK6,X0,sK8(X1,sK6,sK5),sK5)
      | ~ r2_hidden(X0,X1)
      | ~ sP2(X1,sK6,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f172,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( k3_orders_2(X2,X1,X3) != X0
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ( k3_orders_2(X2,X1,sK8(X0,X1,X2)) = X0
          & r2_hidden(sK8(X0,X1,X2),X1)
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X2,X1,X4) = X0
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( k3_orders_2(X2,X1,sK8(X0,X1,X2)) = X0
        & r2_hidden(sK8(X0,X1,X2),X1)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( k3_orders_2(X2,X1,X3) != X0
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
      & ( ? [X4] :
            ( k3_orders_2(X2,X1,X4) = X0
            & r2_hidden(X4,X1)
            & m1_subset_1(X4,u1_struct_0(X2)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( sP2(X2,X1,X0)
        | ! [X3] :
            ( k3_orders_2(X0,X1,X3) != X2
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X3] :
            ( k3_orders_2(X0,X1,X3) = X2
            & r2_hidden(X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f172,plain,(
    ! [X0,X1] :
      ( sP0(sK6,X0,sK8(X1,sK6,sK5),sK5)
      | ~ r2_hidden(X0,X1)
      | ~ sP2(X1,sK6,sK5)
      | ~ m1_subset_1(sK8(X1,sK6,sK5),u1_struct_0(sK5))
      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ) ),
    inference(resolution,[],[f104,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sP1(sK5,X0,X1,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5)) ) ),
    inference(subsumption_resolution,[],[f137,f49])).

fof(f137,plain,(
    ! [X0,X1] :
      ( sP1(sK5,X0,X1,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f136,f50])).

fof(f136,plain,(
    ! [X0,X1] :
      ( sP1(sK5,X0,X1,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f135,f51])).

fof(f135,plain,(
    ! [X0,X1] :
      ( sP1(sK5,X0,X1,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f134,f52])).

fof(f134,plain,(
    ! [X0,X1] :
      ( sP1(sK5,X0,X1,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f133,f53])).

fof(f133,plain,(
    ! [X0,X1] :
      ( sP1(sK5,X0,X1,sK6)
      | ~ m1_subset_1(X0,u1_struct_0(sK5))
      | ~ m1_subset_1(X1,u1_struct_0(sK5))
      | ~ l1_orders_2(sK5)
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f62,f54])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | sP1(X0,X2,X1,X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP1(X0,X2,X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f12,f21,f20])).

fof(f21,plain,(
    ! [X0,X2,X1,X3] :
      ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
      <=> sP0(X3,X1,X2,X0) )
      | ~ sP1(X0,X2,X1,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,sK8(X2,X1,X0),X3,X1)
      | sP0(X1,X3,sK8(X2,X1,X0),X0)
      | ~ r2_hidden(X3,X2)
      | ~ sP2(X2,X1,X0) ) ),
    inference(superposition,[],[f57,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X2,X1,sK8(X0,X1,X2)) = X0
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k3_orders_2(X0,X3,X1))
      | sP0(X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X2,k3_orders_2(X0,X3,X1))
          | ~ sP0(X3,X2,X1,X0) )
        & ( sP0(X3,X2,X1,X0)
          | ~ r2_hidden(X2,k3_orders_2(X0,X3,X1)) ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X2,X1,X3] :
      ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
          | ~ sP0(X3,X1,X2,X0) )
        & ( sP0(X3,X1,X2,X0)
          | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
      | ~ sP1(X0,X2,X1,X3) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f55,plain,(
    m1_orders_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f480,plain,
    ( ~ m1_orders_2(sK7,sK5,k1_xboole_0)
    | k1_xboole_0 = sK7 ),
    inference(resolution,[],[f419,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ sP4(X0,k1_xboole_0,X2)
      | ~ m1_orders_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ m1_orders_2(X0,X2,X1)
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( m1_orders_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ m1_orders_2(X0,X2,X1) ) )
      | k1_xboole_0 != X1
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ( ( m1_orders_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ m1_orders_2(X2,X0,X1) ) )
      | k1_xboole_0 != X1
      | ~ sP4(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f419,plain,(
    sP4(sK7,k1_xboole_0,sK5) ),
    inference(backward_demodulation,[],[f220,f369])).

fof(f220,plain,(
    sP4(sK7,sK6,sK5) ),
    inference(resolution,[],[f212,f55])).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK5,sK6)
      | sP4(X0,sK6,sK5) ) ),
    inference(resolution,[],[f164,f54])).

fof(f164,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5)))
      | sP4(X8,X9,sK5)
      | ~ m1_orders_2(X8,sK5,sK6) ) ),
    inference(subsumption_resolution,[],[f163,f49])).

fof(f163,plain,(
    ! [X8,X9] :
      ( ~ m1_orders_2(X8,sK5,sK6)
      | sP4(X8,X9,sK5)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5)))
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f162,f50])).

fof(f162,plain,(
    ! [X8,X9] :
      ( ~ m1_orders_2(X8,sK5,sK6)
      | sP4(X8,X9,sK5)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f161,f51])).

fof(f161,plain,(
    ! [X8,X9] :
      ( ~ m1_orders_2(X8,sK5,sK6)
      | sP4(X8,X9,sK5)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f160,f52])).

fof(f160,plain,(
    ! [X8,X9] :
      ( ~ m1_orders_2(X8,sK5,sK6)
      | sP4(X8,X9,sK5)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(subsumption_resolution,[],[f143,f53])).

fof(f143,plain,(
    ! [X8,X9] :
      ( ~ m1_orders_2(X8,sK5,sK6)
      | sP4(X8,X9,sK5)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5)))
      | ~ l1_orders_2(sK5)
      | ~ v5_orders_2(sK5)
      | ~ v4_orders_2(sK5)
      | ~ v3_orders_2(sK5)
      | v2_struct_0(sK5) ) ),
    inference(resolution,[],[f126,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | sP4(X2,X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f382,plain,(
    ~ r1_tarski(sK7,k1_xboole_0) ),
    inference(backward_demodulation,[],[f56,f369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (25051)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (25067)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (25060)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (25052)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (25060)Refutation not found, incomplete strategy% (25060)------------------------------
% 0.21/0.53  % (25060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25060)Memory used [KB]: 10746
% 0.21/0.53  % (25060)Time elapsed: 0.010 s
% 0.21/0.53  % (25060)------------------------------
% 0.21/0.53  % (25060)------------------------------
% 0.21/0.53  % (25067)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f515,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f512,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(flattening,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f512,plain,(
% 0.21/0.53    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f382,f481])).
% 0.21/0.53  fof(f481,plain,(
% 0.21/0.53    k1_xboole_0 = sK7),
% 0.21/0.53    inference(subsumption_resolution,[],[f480,f381])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    m1_orders_2(sK7,sK5,k1_xboole_0)),
% 0.21/0.53    inference(backward_demodulation,[],[f55,f369])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    k1_xboole_0 = sK6),
% 0.21/0.53    inference(subsumption_resolution,[],[f368,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~r1_tarski(sK7,sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ((~r1_tarski(sK7,sK6) & m1_orders_2(sK7,sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f10,f29,f28,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,sK5,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) & l1_orders_2(sK5) & v5_orders_2(sK5) & v4_orders_2(sK5) & v3_orders_2(sK5) & ~v2_struct_0(sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,sK5,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))) => (? [X2] : (~r1_tarski(X2,sK6) & m1_orders_2(X2,sK5,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ? [X2] : (~r1_tarski(X2,sK6) & m1_orders_2(X2,sK5,sK6)) => (~r1_tarski(sK7,sK6) & m1_orders_2(sK7,sK5,sK6))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    k1_xboole_0 = sK6 | r1_tarski(sK7,sK6)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f366])).
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    k1_xboole_0 = sK6 | r1_tarski(sK7,sK6) | r1_tarski(sK7,sK6)),
% 0.21/0.53    inference(resolution,[],[f290,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK9(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f46,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(rectify,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f290,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK9(sK7,X0),sK6) | k1_xboole_0 = sK6 | r1_tarski(sK7,X0)) )),
% 0.21/0.53    inference(resolution,[],[f287,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f48])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK7) | r2_hidden(X2,sK6) | k1_xboole_0 = sK6) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f286,f183])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK5)) | ~r2_hidden(X0,sK7)) )),
% 0.21/0.53    inference(resolution,[],[f144,f55])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X10,X11] : (~m1_orders_2(X10,sK5,sK6) | m1_subset_1(X11,u1_struct_0(sK5)) | ~r2_hidden(X11,X10)) )),
% 0.21/0.53    inference(resolution,[],[f126,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~m1_orders_2(X0,sK5,sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f125,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ~v2_struct_0(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f124,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    v3_orders_2(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f123,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    v4_orders_2(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f52])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    v5_orders_2(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f121,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    l1_orders_2(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_orders_2(sK5) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(resolution,[],[f73,f54])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_orders_2)).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    ( ! [X2] : (~r2_hidden(X2,sK7) | ~m1_subset_1(X2,u1_struct_0(sK5)) | r2_hidden(X2,sK6) | k1_xboole_0 = sK6) )),
% 0.21/0.53    inference(resolution,[],[f231,f251])).
% 0.21/0.53  fof(f251,plain,(
% 0.21/0.53    sP2(sK7,sK6,sK5) | k1_xboole_0 = sK6),
% 0.21/0.53    inference(subsumption_resolution,[],[f250,f55])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    k1_xboole_0 = sK6 | ~m1_orders_2(sK7,sK5,sK6) | sP2(sK7,sK6,sK5)),
% 0.21/0.53    inference(resolution,[],[f240,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | ~m1_orders_2(X2,X0,X1) | sP2(X2,X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((m1_orders_2(X2,X0,X1) | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | ~m1_orders_2(X2,X0,X1))) | ~sP3(X0,X1,X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_orders_2(X2,X0,X1) <=> sP2(X2,X1,X0)) | ~sP3(X0,X1,X2))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    sP3(sK5,sK6,sK7) | k1_xboole_0 = sK6),
% 0.21/0.53    inference(resolution,[],[f217,f55])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | sP3(sK5,sK6,X0) | k1_xboole_0 = sK6) )),
% 0.21/0.53    inference(resolution,[],[f154,f54])).
% 0.21/0.53  fof(f154,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) | k1_xboole_0 = X5 | sP3(sK5,X5,X4) | ~m1_orders_2(X4,sK5,sK6)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f153,f49])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_orders_2(X4,sK5,sK6) | k1_xboole_0 = X5 | sP3(sK5,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f152,f50])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_orders_2(X4,sK5,sK6) | k1_xboole_0 = X5 | sP3(sK5,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f151,f51])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_orders_2(X4,sK5,sK6) | k1_xboole_0 = X5 | sP3(sK5,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f52])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_orders_2(X4,sK5,sK6) | k1_xboole_0 = X5 | sP3(sK5,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f53])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~m1_orders_2(X4,sK5,sK6) | k1_xboole_0 = X5 | sP3(sK5,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_orders_2(sK5) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.53    inference(resolution,[],[f126,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | sP3(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((sP4(X2,X1,X0) & (sP3(X0,X1,X2) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f14,f25,f24,f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (sP2(X2,X1,X0) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X2,X1,X0] : ((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~sP2(X3,sK6,sK5) | ~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK5)) | r2_hidden(X2,sK6)) )),
% 0.21/0.53    inference(resolution,[],[f173,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r2_hidden(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ~r2_hidden(X1,X0) | ~r2_orders_2(X3,X1,X2)) & ((r2_hidden(X1,X0) & r2_orders_2(X3,X1,X2)) | ~sP0(X0,X1,X2,X3)))),
% 0.21/0.53    inference(rectify,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X3,X1,X2,X0] : ((sP0(X3,X1,X2,X0) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~sP0(X3,X1,X2,X0)))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X3,X1,X2,X0] : ((sP0(X3,X1,X2,X0) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~sP0(X3,X1,X2,X0)))),
% 0.21/0.53    inference(nnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X3,X1,X2,X0] : (sP0(X3,X1,X2,X0) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(sK6,X0,sK8(X1,sK6,sK5),sK5) | ~r2_hidden(X0,X1) | ~sP2(X1,sK6,sK5) | ~m1_subset_1(X0,u1_struct_0(sK5))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f172,f67])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2)) | ~sP2(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (k3_orders_2(X2,X1,X3) != X0 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X2)))) & ((k3_orders_2(X2,X1,sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f40,f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X2,X1,X4) = X0 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X2))) => (k3_orders_2(X2,X1,sK8(X0,X1,X2)) = X0 & r2_hidden(sK8(X0,X1,X2),X1) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ! [X3] : (k3_orders_2(X2,X1,X3) != X0 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X2)))) & (? [X4] : (k3_orders_2(X2,X1,X4) = X0 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.54    inference(rectify,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((sP2(X2,X1,X0) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X2,X1,X0)))),
% 0.21/0.54    inference(nnf_transformation,[],[f23])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP0(sK6,X0,sK8(X1,sK6,sK5),sK5) | ~r2_hidden(X0,X1) | ~sP2(X1,sK6,sK5) | ~m1_subset_1(sK8(X1,sK6,sK5),u1_struct_0(sK5)) | ~m1_subset_1(X0,u1_struct_0(sK5))) )),
% 0.21/0.54    inference(resolution,[],[f104,f138])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(sK5,X0,X1,sK6) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5))) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f137,f49])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(sK5,X0,X1,sK6) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f136,f50])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(sK5,X0,X1,sK6) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f135,f51])).
% 0.21/0.54  fof(f135,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(sK5,X0,X1,sK6) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f134,f52])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(sK5,X0,X1,sK6) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f133,f53])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP1(sK5,X0,X1,sK6) | ~m1_subset_1(X0,u1_struct_0(sK5)) | ~m1_subset_1(X1,u1_struct_0(sK5)) | ~l1_orders_2(sK5) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(resolution,[],[f62,f54])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | sP1(X0,X2,X1,X3) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP1(X0,X2,X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(definition_folding,[],[f12,f21,f20])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X2,X1,X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> sP0(X3,X1,X2,X0)) | ~sP1(X0,X2,X1,X3))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~sP1(X0,sK8(X2,X1,X0),X3,X1) | sP0(X1,X3,sK8(X2,X1,X0),X0) | ~r2_hidden(X3,X2) | ~sP2(X2,X1,X0)) )),
% 0.21/0.54    inference(superposition,[],[f57,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k3_orders_2(X2,X1,sK8(X0,X1,X2)) = X0 | ~sP2(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f42])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,k3_orders_2(X0,X3,X1)) | sP0(X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_hidden(X2,k3_orders_2(X0,X3,X1)) | ~sP0(X3,X2,X1,X0)) & (sP0(X3,X2,X1,X0) | ~r2_hidden(X2,k3_orders_2(X0,X3,X1)))) | ~sP1(X0,X1,X2,X3))),
% 0.21/0.54    inference(rectify,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0,X2,X1,X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~sP0(X3,X1,X2,X0)) & (sP0(X3,X1,X2,X0) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~sP1(X0,X2,X1,X3))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    m1_orders_2(sK7,sK5,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f30])).
% 0.21/0.54  fof(f480,plain,(
% 0.21/0.54    ~m1_orders_2(sK7,sK5,k1_xboole_0) | k1_xboole_0 = sK7),
% 0.21/0.54    inference(resolution,[],[f419,f83])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~sP4(X0,k1_xboole_0,X2) | ~m1_orders_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f63])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~m1_orders_2(X0,X2,X1) | k1_xboole_0 != X1 | ~sP4(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((m1_orders_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~m1_orders_2(X0,X2,X1))) | k1_xboole_0 != X1 | ~sP4(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1 | ~sP4(X2,X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f419,plain,(
% 0.21/0.54    sP4(sK7,k1_xboole_0,sK5)),
% 0.21/0.54    inference(backward_demodulation,[],[f220,f369])).
% 0.21/0.54  fof(f220,plain,(
% 0.21/0.54    sP4(sK7,sK6,sK5)),
% 0.21/0.54    inference(resolution,[],[f212,f55])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_orders_2(X0,sK5,sK6) | sP4(X0,sK6,sK5)) )),
% 0.21/0.54    inference(resolution,[],[f164,f54])).
% 0.21/0.54  fof(f164,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5))) | sP4(X8,X9,sK5) | ~m1_orders_2(X8,sK5,sK6)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f163,f49])).
% 0.21/0.54  fof(f163,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~m1_orders_2(X8,sK5,sK6) | sP4(X8,X9,sK5) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5))) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f162,f50])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~m1_orders_2(X8,sK5,sK6) | sP4(X8,X9,sK5) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5))) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f161,f51])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~m1_orders_2(X8,sK5,sK6) | sP4(X8,X9,sK5) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5))) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f160,f52])).
% 0.21/0.54  fof(f160,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~m1_orders_2(X8,sK5,sK6) | sP4(X8,X9,sK5) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5))) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f143,f53])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    ( ! [X8,X9] : (~m1_orders_2(X8,sK5,sK6) | sP4(X8,X9,sK5) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK5))) | ~l1_orders_2(sK5) | ~v5_orders_2(sK5) | ~v4_orders_2(sK5) | ~v3_orders_2(sK5) | v2_struct_0(sK5)) )),
% 0.21/0.54    inference(resolution,[],[f126,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | sP4(X2,X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f26])).
% 0.21/0.54  fof(f382,plain,(
% 0.21/0.54    ~r1_tarski(sK7,k1_xboole_0)),
% 0.21/0.54    inference(backward_demodulation,[],[f56,f369])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (25067)------------------------------
% 0.21/0.54  % (25067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25067)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (25067)Memory used [KB]: 2046
% 0.21/0.54  % (25067)Time elapsed: 0.096 s
% 0.21/0.54  % (25067)------------------------------
% 0.21/0.54  % (25067)------------------------------
% 0.21/0.54  % (25037)Success in time 0.171 s
%------------------------------------------------------------------------------
