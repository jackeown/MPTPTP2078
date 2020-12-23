%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0022+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LN7MnCIYPB

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:11 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  111 ( 163 expanded)
%              Number of equality atoms :   22 (  36 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t15_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_xboole_0 @ A @ B )
        = k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_xboole_0 @ A @ B )
          = k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t15_xboole_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1'])).

thf(fc5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ~ ( v1_xboole_0 @ ( k2_xboole_0 @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[fc5_xboole_0])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['5','6'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( ( X3 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ o_0_0_xboole_0 )
      = X2 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    sk_A = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['2','11','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    sk_A != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','18'])).


%------------------------------------------------------------------------------
