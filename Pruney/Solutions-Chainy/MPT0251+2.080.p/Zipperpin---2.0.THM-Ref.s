%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.91Qeag4Fva

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:12 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   70 (  93 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :  432 ( 610 expanded)
%              Number of equality atoms :   39 (  59 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X37 @ X39 ) @ X40 )
      | ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( r2_hidden @ X37 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('6',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','5'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('23',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','31'])).

thf('33',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['10','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ X21 @ ( k4_xboole_0 @ X22 @ X21 ) )
      = ( k2_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('38',plain,(
    ! [X18: $i] :
      ( ( k2_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36','39'])).

thf('41',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.91Qeag4Fva
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:52:03 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 295 iterations in 0.167s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(t46_zfmisc_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r2_hidden @ A @ B ) =>
% 0.41/0.62       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i]:
% 0.41/0.62        ( ( r2_hidden @ A @ B ) =>
% 0.41/0.62          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.41/0.62  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t38_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.41/0.62       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X37 : $i, X39 : $i, X40 : $i]:
% 0.41/0.62         ((r1_tarski @ (k2_tarski @ X37 @ X39) @ X40)
% 0.41/0.62          | ~ (r2_hidden @ X39 @ X40)
% 0.41/0.62          | ~ (r2_hidden @ X37 @ X40))),
% 0.41/0.62      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.62          | (r1_tarski @ (k2_tarski @ X0 @ sk_A) @ sk_B_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)),
% 0.41/0.62      inference('sup-', [status(thm)], ['0', '3'])).
% 0.41/0.62  thf(t69_enumset1, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.62  thf('5', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.41/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.62  thf('6', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf(t28_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i]:
% 0.41/0.62         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.41/0.62  thf(t100_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X16 @ X17)
% 0.41/0.62           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.41/0.62         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['8', '9'])).
% 0.41/0.62  thf(d10_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.41/0.62  thf('12', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 0.41/0.62      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X19 : $i, X20 : $i]:
% 0.41/0.62         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 0.41/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.62  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X16 @ X17)
% 0.41/0.62           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf(t7_xboole_0, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X12 : $i]:
% 0.41/0.62         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.41/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.41/0.62  thf(t1_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.41/0.62       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         ((r2_hidden @ X8 @ X9)
% 0.41/0.62          | (r2_hidden @ X8 @ X10)
% 0.41/0.62          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.41/0.62          | (r2_hidden @ X1 @ X0)
% 0.41/0.62          | (r2_hidden @ X1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.62  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X16 @ X17)
% 0.41/0.62           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X8 @ X9)
% 0.41/0.62          | ~ (r2_hidden @ X8 @ X10)
% 0.41/0.62          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.41/0.62          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.62          | ~ (r2_hidden @ X2 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.62  thf(d4_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.41/0.62       ( ![D:$i]:
% 0.41/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.62           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X6 @ X5)
% 0.41/0.62          | (r2_hidden @ X6 @ X3)
% 0.41/0.62          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.41/0.62         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.41/0.62      inference('simplify', [status(thm)], ['26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.62          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.62      inference('clc', [status(thm)], ['25', '27'])).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X1 @ X0)
% 0.41/0.62          | ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['22', '28'])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('clc', [status(thm)], ['21', '29'])).
% 0.41/0.62  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '30'])).
% 0.41/0.62  thf('32', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 0.41/0.62      inference('demod', [status(thm)], ['16', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))),
% 0.41/0.62      inference('demod', [status(thm)], ['10', '32'])).
% 0.41/0.62  thf(t39_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (![X21 : $i, X22 : $i]:
% 0.41/0.62         ((k2_xboole_0 @ X21 @ (k4_xboole_0 @ X22 @ X21))
% 0.41/0.62           = (k2_xboole_0 @ X21 @ X22))),
% 0.41/0.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.41/0.62         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['33', '34'])).
% 0.41/0.62  thf(commutativity_k2_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.62  thf(t1_boole, axiom,
% 0.41/0.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.62  thf('38', plain, (![X18 : $i]: ((k2_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.62  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.41/0.62      inference('demod', [status(thm)], ['35', '36', '39'])).
% 0.41/0.62  thf('41', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.41/0.62  thf('43', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.62  thf('44', plain, ($false),
% 0.41/0.62      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.47/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
