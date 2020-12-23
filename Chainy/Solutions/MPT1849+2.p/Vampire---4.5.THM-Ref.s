%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1849+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:34 EST 2020

% Result     : Theorem 4.05s
% Output     : Refutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 342 expanded)
%              Number of leaves         :    9 ( 104 expanded)
%              Depth                    :   18
%              Number of atoms          :  194 (1695 expanded)
%              Number of equality atoms :   50 ( 370 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18743,plain,(
    $false ),
    inference(subsumption_resolution,[],[f18733,f4219])).

fof(f4219,plain,(
    l1_pre_topc(sK10) ),
    inference(cnf_transformation,[],[f3973])).

fof(f3973,plain,
    ( g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10)) != g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11))
    & m1_pre_topc(sK11,sK10)
    & ~ v1_tex_2(sK11,sK10)
    & l1_pre_topc(sK10)
    & ~ v2_struct_0(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f3622,f3972,f3971])).

fof(f3971,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10))
          & m1_pre_topc(X1,sK10)
          & ~ v1_tex_2(X1,sK10) )
      & l1_pre_topc(sK10)
      & ~ v2_struct_0(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f3972,plain,
    ( ? [X1] :
        ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10))
        & m1_pre_topc(X1,sK10)
        & ~ v1_tex_2(X1,sK10) )
   => ( g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10)) != g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11))
      & m1_pre_topc(sK11,sK10)
      & ~ v1_tex_2(sK11,sK10) ) ),
    introduced(choice_axiom,[])).

fof(f3622,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3621])).

fof(f3621,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3604])).

fof(f3604,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f3603])).

fof(f3603,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tex_2)).

fof(f18733,plain,(
    ~ l1_pre_topc(sK10) ),
    inference(resolution,[],[f18731,f4329])).

fof(f4329,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3691])).

fof(f3691,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3456])).

fof(f3456,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f18731,plain,(
    ~ m1_pre_topc(sK10,sK10) ),
    inference(subsumption_resolution,[],[f18730,f7265])).

fof(f7265,plain,(
    g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10)) != g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK11)) ),
    inference(backward_demodulation,[],[f4222,f7260])).

fof(f7260,plain,(
    u1_struct_0(sK10) = u1_struct_0(sK11) ),
    inference(global_subsumption,[],[f5416,f7251])).

fof(f7251,plain,
    ( u1_struct_0(sK10) = u1_struct_0(sK11)
    | ~ m1_subset_1(u1_struct_0(sK11),k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(resolution,[],[f7240,f4688])).

fof(f4688,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f4203])).

fof(f4203,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f3910])).

fof(f3910,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3572])).

fof(f3572,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f7240,plain,(
    ~ v1_subset_1(u1_struct_0(sK11),u1_struct_0(sK10)) ),
    inference(forward_demodulation,[],[f5282,f5280])).

fof(f5280,plain,(
    u1_struct_0(sK11) = sK25(sK10,sK11) ),
    inference(global_subsumption,[],[f4221,f5279])).

fof(f5279,plain,
    ( u1_struct_0(sK11) = sK25(sK10,sK11)
    | ~ m1_pre_topc(sK11,sK10) ),
    inference(subsumption_resolution,[],[f5263,f4219])).

fof(f5263,plain,
    ( u1_struct_0(sK11) = sK25(sK10,sK11)
    | ~ m1_pre_topc(sK11,sK10)
    | ~ l1_pre_topc(sK10) ),
    inference(resolution,[],[f4220,f4348])).

fof(f4348,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK25(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4022])).

fof(f4022,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK25(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK25(X0,X1)
                & m1_subset_1(sK25(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f4020,f4021])).

fof(f4021,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK25(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK25(X0,X1)
        & m1_subset_1(sK25(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f4020,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f4019])).

fof(f4019,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f3709])).

fof(f3709,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3708])).

fof(f3708,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3571])).

fof(f3571,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tex_2)).

fof(f4220,plain,(
    ~ v1_tex_2(sK11,sK10) ),
    inference(cnf_transformation,[],[f3973])).

fof(f4221,plain,(
    m1_pre_topc(sK11,sK10) ),
    inference(cnf_transformation,[],[f3973])).

fof(f5282,plain,(
    ~ v1_subset_1(sK25(sK10,sK11),u1_struct_0(sK10)) ),
    inference(global_subsumption,[],[f4221,f5281])).

fof(f5281,plain,
    ( ~ v1_subset_1(sK25(sK10,sK11),u1_struct_0(sK10))
    | ~ m1_pre_topc(sK11,sK10) ),
    inference(subsumption_resolution,[],[f5264,f4219])).

fof(f5264,plain,
    ( ~ v1_subset_1(sK25(sK10,sK11),u1_struct_0(sK10))
    | ~ m1_pre_topc(sK11,sK10)
    | ~ l1_pre_topc(sK10) ),
    inference(resolution,[],[f4220,f4349])).

fof(f4349,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK25(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f4022])).

fof(f5416,plain,(
    m1_subset_1(u1_struct_0(sK11),k1_zfmisc_1(u1_struct_0(sK10))) ),
    inference(subsumption_resolution,[],[f5315,f4219])).

fof(f5315,plain,
    ( m1_subset_1(u1_struct_0(sK11),k1_zfmisc_1(u1_struct_0(sK10)))
    | ~ l1_pre_topc(sK10) ),
    inference(resolution,[],[f4221,f4326])).

fof(f4326,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3688])).

fof(f3688,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3573])).

fof(f3573,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l17_tex_2)).

fof(f4222,plain,(
    g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10)) != g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11)) ),
    inference(cnf_transformation,[],[f3973])).

fof(f18730,plain,
    ( g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK10)) = g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK11))
    | ~ m1_pre_topc(sK10,sK10) ),
    inference(equality_resolution,[],[f18530])).

fof(f18530,plain,(
    ! [X5] :
      ( u1_struct_0(sK10) != u1_struct_0(X5)
      | g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) = g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK11))
      | ~ m1_pre_topc(X5,sK10) ) ),
    inference(forward_demodulation,[],[f18529,f7260])).

fof(f18529,plain,(
    ! [X5] :
      ( g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) = g1_pre_topc(u1_struct_0(sK10),u1_pre_topc(sK11))
      | u1_struct_0(sK11) != u1_struct_0(X5)
      | ~ m1_pre_topc(X5,sK10) ) ),
    inference(forward_demodulation,[],[f5403,f7260])).

fof(f5403,plain,(
    ! [X5] :
      ( g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11)) = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
      | u1_struct_0(sK11) != u1_struct_0(X5)
      | ~ m1_pre_topc(X5,sK10) ) ),
    inference(subsumption_resolution,[],[f5291,f4219])).

fof(f5291,plain,(
    ! [X5] :
      ( g1_pre_topc(u1_struct_0(sK11),u1_pre_topc(sK11)) = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))
      | u1_struct_0(sK11) != u1_struct_0(X5)
      | ~ m1_pre_topc(X5,sK10)
      | ~ l1_pre_topc(sK10) ) ),
    inference(resolution,[],[f4221,f4253])).

fof(f4253,plain,(
    ! [X2,X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | u1_struct_0(X1) != u1_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3649])).

fof(f3649,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f3648])).

fof(f3648,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3492])).

fof(f3492,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_tsep_1)).
%------------------------------------------------------------------------------
