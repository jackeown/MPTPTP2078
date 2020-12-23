%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1111+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:07 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   34 (  55 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 221 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3470,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3469,f2614])).

fof(f2614,plain,(
    l1_pre_topc(sK52) ),
    inference(cnf_transformation,[],[f2325])).

fof(f2325,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK53)
        | ~ m1_subset_1(X2,u1_struct_0(sK52)) )
    & k1_struct_0(sK52) != sK53
    & m1_subset_1(sK53,k1_zfmisc_1(u1_struct_0(sK52)))
    & l1_pre_topc(sK52) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK52,sK53])],[f1824,f2324,f2323])).

fof(f2323,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ! [X2] :
                ( ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & k1_struct_0(X0) != X1
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(sK52)) )
          & k1_struct_0(sK52) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK52))) )
      & l1_pre_topc(sK52) ) ),
    introduced(choice_axiom,[])).

fof(f2324,plain,
    ( ? [X1] :
        ( ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(sK52)) )
        & k1_struct_0(sK52) != X1
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK52))) )
   => ( ! [X2] :
          ( ~ r2_hidden(X2,sK53)
          | ~ m1_subset_1(X2,u1_struct_0(sK52)) )
      & k1_struct_0(sK52) != sK53
      & m1_subset_1(sK53,k1_zfmisc_1(u1_struct_0(sK52))) ) ),
    introduced(choice_axiom,[])).

fof(f1824,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1823])).

fof(f1823,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          & k1_struct_0(X0) != X1
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1816])).

fof(f1816,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( ! [X2] :
                    ( m1_subset_1(X2,u1_struct_0(X0))
                   => ~ r2_hidden(X2,X1) )
                & k1_struct_0(X0) != X1 ) ) ) ),
    inference(negated_conjecture,[],[f1815])).

fof(f1815,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ r2_hidden(X2,X1) )
              & k1_struct_0(X0) != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_pre_topc)).

fof(f3469,plain,(
    ~ l1_pre_topc(sK52) ),
    inference(resolution,[],[f3468,f2671])).

fof(f2671,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1861])).

fof(f1861,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1776])).

fof(f1776,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f3468,plain,(
    ~ l1_struct_0(sK52) ),
    inference(trivial_inequality_removal,[],[f3467])).

fof(f3467,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ l1_struct_0(sK52) ),
    inference(superposition,[],[f3462,f2659])).

fof(f2659,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f1850])).

fof(f1850,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1769])).

fof(f1769,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k1_xboole_0 = k1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_struct_0)).

fof(f3462,plain,(
    k1_xboole_0 != k1_struct_0(sK52) ),
    inference(backward_demodulation,[],[f2616,f3418])).

fof(f3418,plain,(
    k1_xboole_0 = sK53 ),
    inference(resolution,[],[f3407,f2766])).

fof(f2766,plain,(
    ! [X0] :
      ( r2_hidden(sK74(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2405])).

fof(f2405,plain,(
    ! [X0] :
      ( r2_hidden(sK74(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK74])],[f1922,f2404])).

fof(f2404,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK74(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1922,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f3407,plain,(
    ! [X1] : ~ r2_hidden(X1,sK53) ),
    inference(global_subsumption,[],[f2617,f3388])).

fof(f3388,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK52))
      | ~ r2_hidden(X1,sK53) ) ),
    inference(resolution,[],[f2615,f2622])).

fof(f2622,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1830])).

fof(f1830,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1829])).

fof(f1829,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f2615,plain,(
    m1_subset_1(sK53,k1_zfmisc_1(u1_struct_0(sK52))) ),
    inference(cnf_transformation,[],[f2325])).

fof(f2617,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK53)
      | ~ m1_subset_1(X2,u1_struct_0(sK52)) ) ),
    inference(cnf_transformation,[],[f2325])).

fof(f2616,plain,(
    k1_struct_0(sK52) != sK53 ),
    inference(cnf_transformation,[],[f2325])).
%------------------------------------------------------------------------------
