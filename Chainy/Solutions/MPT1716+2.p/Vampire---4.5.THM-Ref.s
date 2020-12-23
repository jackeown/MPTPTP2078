%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1716+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:30 EST 2020

% Result     : Theorem 1.96s
% Output     : Refutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   38 (  90 expanded)
%              Number of leaves         :    7 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  162 ( 502 expanded)
%              Number of equality atoms :   17 (  81 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4429,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4404,f4349])).

fof(f4349,plain,(
    ~ m1_pre_topc(sK5,sK5) ),
    inference(subsumption_resolution,[],[f4348,f3518])).

fof(f3518,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f3462])).

fof(f3462,plain,
    ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k1_tsep_1(sK4,sK5,sK5)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f3377,f3461,f3460])).

fof(f3460,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(X0,X1,X1)
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK4,X1,X1)
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f3461,plain,
    ( ? [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(sK4,X1,X1)
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k1_tsep_1(sK4,sK5,sK5)
      & m1_pre_topc(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f3377,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3376])).

fof(f3376,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != k1_tsep_1(X0,X1,X1)
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3362])).

fof(f3362,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    inference(negated_conjecture,[],[f3361])).

fof(f3361,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f4348,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f4347,f3519])).

fof(f3519,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3462])).

fof(f4347,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f4346,f3520])).

fof(f3520,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f3462])).

fof(f4346,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f4345,f3521])).

fof(f3521,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f3462])).

fof(f4345,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f4344,f3522])).

fof(f3522,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f3462])).

fof(f4344,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(duplicate_literal_removal,[],[f4341])).

fof(f4341,plain,
    ( ~ m1_pre_topc(sK5,sK5)
    | ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ m1_pre_topc(sK5,sK4)
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f3684,f3690])).

fof(f3690,plain,(
    ! [X2,X0,X1] :
      ( sQ29_eqProxy(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f3549,f3683])).

fof(f3683,plain,(
    ! [X1,X0] :
      ( sQ29_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ29_eqProxy])])).

fof(f3549,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3474])).

fof(f3474,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != k1_tsep_1(X0,X1,X2) )
                & ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2)
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f3395])).

fof(f3395,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f3394])).

fof(f3394,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3359])).

fof(f3359,axiom,(
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
              <=> g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k1_tsep_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f3684,plain,(
    ~ sQ29_eqProxy(g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)),k1_tsep_1(sK4,sK5,sK5)) ),
    inference(equality_proxy_replacement,[],[f3523,f3683])).

fof(f3523,plain,(
    g1_pre_topc(u1_struct_0(sK5),u1_pre_topc(sK5)) != k1_tsep_1(sK4,sK5,sK5) ),
    inference(cnf_transformation,[],[f3462])).

fof(f4404,plain,(
    m1_pre_topc(sK5,sK5) ),
    inference(resolution,[],[f4225,f3645])).

fof(f3645,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3451])).

fof(f3451,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3363])).

fof(f3363,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f4225,plain,(
    l1_pre_topc(sK5) ),
    inference(subsumption_resolution,[],[f4081,f3520])).

fof(f4081,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4) ),
    inference(resolution,[],[f3522,f3644])).

fof(f3644,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3450])).

fof(f3450,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1784])).

fof(f1784,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
%------------------------------------------------------------------------------
