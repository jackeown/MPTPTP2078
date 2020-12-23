%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1845+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oGCZRCl9ZY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 4.46s
% Output     : Refutation 4.46s
% Verified   : 
% Statistics : Number of formulae       :   24 (  32 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :  132 ( 284 expanded)
%              Number of equality atoms :    3 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_224_type,type,(
    sk_B_224: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_80_type,type,(
    sk_A_80: $i )).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A @ ( u1_pre_topc @ A ) ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A @ ( u1_pre_topc @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X5949: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X5949 @ ( u1_pre_topc @ X5949 ) ) ) )
      | ~ ( l1_pre_topc @ X5949 )
      | ~ ( v2_pre_topc @ X5949 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf(t12_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A @ ( u1_pre_topc @ A ) ) )
                = ( g1_pre_topc @ ( u1_struct_0 @ B @ ( u1_pre_topc @ B ) ) ) )
              & ( v2_pre_topc @ A ) )
           => ( v2_pre_topc @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A @ ( u1_pre_topc @ A ) ) )
                  = ( g1_pre_topc @ ( u1_struct_0 @ B @ ( u1_pre_topc @ B ) ) ) )
                & ( v2_pre_topc @ A ) )
             => ( v2_pre_topc @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tex_2])).

thf('1',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A_80 @ ( u1_pre_topc @ sk_A_80 ) ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B_224 @ ( u1_pre_topc @ sk_B_224 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t58_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A @ ( u1_pre_topc @ A ) ) ) )
       => ( v2_pre_topc @ A ) ) ) )).

thf('2',plain,(
    ! [X6056: $i] :
      ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X6056 @ ( u1_pre_topc @ X6056 ) ) ) )
      | ( v2_pre_topc @ X6056 )
      | ~ ( l1_pre_topc @ X6056 ) ) ),
    inference(cnf,[status(esa)],[t58_pre_topc])).

thf('3',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A_80 @ ( u1_pre_topc @ sk_A_80 ) ) ) )
    | ~ ( l1_pre_topc @ sk_B_224 )
    | ( v2_pre_topc @ sk_B_224 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_B_224 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A_80 @ ( u1_pre_topc @ sk_A_80 ) ) ) )
    | ( v2_pre_topc @ sk_B_224 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v2_pre_topc @ sk_B_224 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A_80 @ ( u1_pre_topc @ sk_A_80 ) ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v2_pre_topc @ sk_A_80 )
    | ~ ( l1_pre_topc @ sk_A_80 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    v2_pre_topc @ sk_A_80 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_A_80 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['8','9','10'])).

%------------------------------------------------------------------------------
