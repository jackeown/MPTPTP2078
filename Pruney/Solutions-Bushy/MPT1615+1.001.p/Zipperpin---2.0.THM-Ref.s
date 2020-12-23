%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1615+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I1d8LCgBow

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   26 (  30 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :  109 ( 157 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t5_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ A ) ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( u1_pre_topc @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[t5_pre_topc])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t23_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ A ) ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t23_yellow_1])).

thf('5',plain,(
    ( k3_yellow_0 @ ( k2_yellow_1 @ ( u1_pre_topc @ sk_A ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(simplify,[status(thm)],['9'])).


%------------------------------------------------------------------------------
