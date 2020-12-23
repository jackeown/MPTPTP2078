%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1105+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.J3XVEsKo4J

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   41 (  46 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 201 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_22_type,type,(
    sk_A_22: $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X5878: $i] :
      ( ( ( k2_struct_0 @ X5878 )
        = ( u1_struct_0 @ X5878 ) )
      | ~ ( l1_struct_0 @ X5878 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t27_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A @ ( k1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ( ( k2_struct_0 @ A )
          = ( k3_subset_1 @ ( u1_struct_0 @ A @ ( k1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_pre_topc])).

thf('1',plain,(
    ( k2_struct_0 @ sk_A_22 )
 != ( k3_subset_1 @ ( u1_struct_0 @ sk_A_22 @ ( k1_struct_0 @ sk_A_22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    l1_struct_0 @ sk_A_22 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X5885: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X5885 ) )
      | ~ ( l1_struct_0 @ X5885 ) ) ),
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
    ( ( k1_struct_0 @ sk_A_22 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ( k2_struct_0 @ sk_A_22 )
 != ( k3_subset_1 @ ( u1_struct_0 @ sk_A_22 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','8'])).

thf('10',plain,
    ( ( ( k2_struct_0 @ sk_A_22 )
     != ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ o_0_0_xboole_0 ) ) )
    | ~ ( l1_struct_0 @ sk_A_22 ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_A_22 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ( k2_struct_0 @ sk_A_22 )
 != ( k3_subset_1 @ ( k2_struct_0 @ sk_A_22 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ ( A @ ( k1_subset_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X1675: $i] :
      ( ( k2_subset_1 @ X1675 )
      = ( k3_subset_1 @ ( X1675 @ ( k1_subset_1 @ X1675 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('14',plain,(
    ! [X1521: $i] :
      ( ( k2_subset_1 @ X1521 )
      = X1521 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X1502: $i] :
      ( ( k1_subset_1 @ X1502 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X1502: $i] :
      ( ( k1_subset_1 @ X1502 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1675: $i] :
      ( X1675
      = ( k3_subset_1 @ ( X1675 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','17'])).

thf('19',plain,(
    ( k2_struct_0 @ sk_A_22 )
 != ( k2_struct_0 @ sk_A_22 ) ),
    inference(demod,[status(thm)],['12','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
