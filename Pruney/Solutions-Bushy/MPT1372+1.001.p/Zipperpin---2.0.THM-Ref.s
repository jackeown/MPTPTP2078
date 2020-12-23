%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1372+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kkP8UzxdUG

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   27 (  35 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   86 ( 158 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v8_struct_0_type,type,(
    v8_struct_0: $i > $o )).

thf(t27_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_finset_1 @ ( u1_struct_0 @ A ) )
       => ( v1_compts_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( v1_finset_1 @ ( u1_struct_0 @ A ) )
         => ( v1_compts_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_compts_1])).

thf('0',plain,(
    ~ ( v1_compts_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ( v8_struct_0 @ A )
          & ( v2_pre_topc @ A ) )
       => ( ( v2_pre_topc @ A )
          & ( v1_compts_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v8_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v1_compts_1 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc3_compts_1])).

thf('3',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_compts_1 @ sk_A )
    | ~ ( v8_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_finset_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v8_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_finset_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ~ ( v1_finset_1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v8_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc9_struct_0])).

thf('7',plain,
    ( ( v8_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v8_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    v1_compts_1 @ sk_A ),
    inference(demod,[status(thm)],['3','4','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).


%------------------------------------------------------------------------------
