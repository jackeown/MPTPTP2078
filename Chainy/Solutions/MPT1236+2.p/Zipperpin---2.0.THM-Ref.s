%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1236+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WAJLfv4DRF

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :   35 (  71 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 314 expanded)
%              Number of equality atoms :   15 (  39 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_31_type,type,(
    sk_A_31: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t47_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k1_tops_1 @ ( A @ ( k1_struct_0 @ A ) ) )
        = ( k1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k1_tops_1 @ ( A @ ( k1_struct_0 @ A ) ) )
          = ( k1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t47_tops_1])).

thf('0',plain,(
    l1_pre_topc @ sk_A_31 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('1',plain,(
    ! [X5930: $i] :
      ( ( l1_struct_0 @ X5930 )
      | ~ ( l1_pre_topc @ X5930 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('2',plain,(
    l1_struct_0 @ sk_A_31 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X5945: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X5945 ) )
      | ~ ( l1_struct_0 @ X5945 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k1_struct_0 @ sk_A_31 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','7'])).

thf(fc8_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( v1_xboole_0 @ ( k1_tops_1 @ ( A @ ( k1_struct_0 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X6723: $i] :
      ( ( v1_xboole_0 @ ( k1_tops_1 @ ( X6723 @ ( k1_struct_0 @ X6723 ) ) ) )
      | ~ ( l1_pre_topc @ X6723 ) ) ),
    inference(cnf,[status(esa)],[fc8_tops_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ ( sk_A_31 @ o_0_0_xboole_0 ) ) )
    | ~ ( l1_pre_topc @ sk_A_31 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A_31 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ ( sk_A_31 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('14',plain,
    ( ( k1_tops_1 @ ( sk_A_31 @ o_0_0_xboole_0 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k1_tops_1 @ ( sk_A_31 @ ( k1_struct_0 @ sk_A_31 ) ) )
 != ( k1_struct_0 @ sk_A_31 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_struct_0 @ sk_A_31 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','7'])).

thf('17',plain,
    ( ( k1_struct_0 @ sk_A_31 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','7'])).

thf('18',plain,(
    ( k1_tops_1 @ ( sk_A_31 @ o_0_0_xboole_0 ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','18'])).

%------------------------------------------------------------------------------
