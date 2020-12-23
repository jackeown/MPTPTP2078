%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M9JDyOgPoo

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:47 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 147 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  436 (1054 expanded)
%              Number of equality atoms :   18 (  46 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X18 ) @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('7',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X17 ) @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('9',plain,(
    ! [X17: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( r1_tarski @ ( k3_subset_1 @ X22 @ X21 ) @ ( k3_subset_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X20: $i] :
      ( ( k2_subset_1 @ X20 )
      = ( k3_subset_1 @ X20 @ ( k1_subset_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('16',plain,(
    ! [X16: $i] :
      ( ( k2_subset_1 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('17',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('18',plain,(
    ! [X20: $i] :
      ( X20
      = ( k3_subset_1 @ X20 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['13','14','18'])).

thf('20',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X10 ) @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('25',plain,(
    r1_tarski @ ( k1_zfmisc_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','27'])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('31',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('34',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('38',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t38_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k3_subset_1 @ X24 @ X25 ) )
      | ( X25
        = ( k1_subset_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t38_subset_1])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( k1_subset_1 @ X15 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('41',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X25 @ ( k3_subset_1 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('44',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M9JDyOgPoo
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:12:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.58/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.77  % Solved by: fo/fo7.sh
% 0.58/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.77  % done 864 iterations in 0.308s
% 0.58/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.77  % SZS output start Refutation
% 0.58/0.77  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.58/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.77  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.58/0.77  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.58/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.77  thf(dt_k2_subset_1, axiom,
% 0.58/0.77    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.77  thf('0', plain,
% 0.58/0.77      (![X18 : $i]: (m1_subset_1 @ (k2_subset_1 @ X18) @ (k1_zfmisc_1 @ X18))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.58/0.77  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.58/0.77  thf('1', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.77  thf('2', plain, (![X18 : $i]: (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X18))),
% 0.58/0.77      inference('demod', [status(thm)], ['0', '1'])).
% 0.58/0.77  thf(d2_subset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( ( v1_xboole_0 @ A ) =>
% 0.58/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.58/0.77       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.58/0.77         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.58/0.77  thf('3', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X12 @ X13)
% 0.58/0.77          | (r2_hidden @ X12 @ X13)
% 0.58/0.77          | (v1_xboole_0 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.77  thf('4', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.58/0.77          | (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.77  thf(fc1_subset_1, axiom,
% 0.58/0.77    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.77  thf('5', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.58/0.77      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.58/0.77  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.58/0.77      inference('clc', [status(thm)], ['4', '5'])).
% 0.58/0.77  thf(dt_k1_subset_1, axiom,
% 0.58/0.77    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.58/0.77  thf('7', plain,
% 0.58/0.77      (![X17 : $i]: (m1_subset_1 @ (k1_subset_1 @ X17) @ (k1_zfmisc_1 @ X17))),
% 0.58/0.77      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.58/0.77  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.58/0.77  thf('8', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.58/0.77  thf('9', plain,
% 0.58/0.77      (![X17 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X17))),
% 0.58/0.77      inference('demod', [status(thm)], ['7', '8'])).
% 0.58/0.77  thf(t40_subset_1, conjecture,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.58/0.77         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.58/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.77        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77          ( ( ( r1_tarski @ B @ C ) & 
% 0.58/0.77              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.58/0.77            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.58/0.77    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.58/0.77  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t31_subset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77       ( ![C:$i]:
% 0.58/0.77         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77           ( ( r1_tarski @ B @ C ) <=>
% 0.58/0.77             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.58/0.77  thf('11', plain,
% 0.58/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22))
% 0.58/0.77          | ~ (r1_tarski @ X23 @ X21)
% 0.58/0.77          | (r1_tarski @ (k3_subset_1 @ X22 @ X21) @ (k3_subset_1 @ X22 @ X23))
% 0.58/0.77          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.58/0.77  thf('12', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.58/0.77          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.58/0.77             (k3_subset_1 @ sk_A @ X0))
% 0.58/0.77          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf('13', plain,
% 0.58/0.77      ((~ (r1_tarski @ k1_xboole_0 @ sk_C_1)
% 0.58/0.77        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.58/0.77           (k3_subset_1 @ sk_A @ k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['9', '12'])).
% 0.58/0.77  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.77  thf('14', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.58/0.77      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.77  thf(t22_subset_1, axiom,
% 0.58/0.77    (![A:$i]:
% 0.58/0.77     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.58/0.77  thf('15', plain,
% 0.58/0.77      (![X20 : $i]:
% 0.58/0.77         ((k2_subset_1 @ X20) = (k3_subset_1 @ X20 @ (k1_subset_1 @ X20)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.58/0.77  thf('16', plain, (![X16 : $i]: ((k2_subset_1 @ X16) = (X16))),
% 0.58/0.77      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.58/0.77  thf('17', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.58/0.77  thf('18', plain, (![X20 : $i]: ((X20) = (k3_subset_1 @ X20 @ k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.58/0.77  thf('19', plain, ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.58/0.77      inference('demod', [status(thm)], ['13', '14', '18'])).
% 0.58/0.77  thf('20', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf(t1_xboole_1, axiom,
% 0.58/0.77    (![A:$i,B:$i,C:$i]:
% 0.58/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.58/0.77       ( r1_tarski @ A @ C ) ))).
% 0.58/0.77  thf('21', plain,
% 0.58/0.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X4 @ X5)
% 0.58/0.77          | ~ (r1_tarski @ X5 @ X6)
% 0.58/0.77          | (r1_tarski @ X4 @ X6))),
% 0.58/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.58/0.77  thf('22', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ sk_B @ X0)
% 0.58/0.77          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('23', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.58/0.77      inference('sup-', [status(thm)], ['19', '22'])).
% 0.58/0.77  thf(t79_zfmisc_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ B ) =>
% 0.58/0.77       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.58/0.77  thf('24', plain,
% 0.58/0.77      (![X10 : $i, X11 : $i]:
% 0.58/0.77         ((r1_tarski @ (k1_zfmisc_1 @ X10) @ (k1_zfmisc_1 @ X11))
% 0.58/0.77          | ~ (r1_tarski @ X10 @ X11))),
% 0.58/0.77      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.58/0.77  thf('25', plain, ((r1_tarski @ (k1_zfmisc_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['23', '24'])).
% 0.58/0.77  thf(d3_tarski, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( r1_tarski @ A @ B ) <=>
% 0.58/0.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.58/0.77  thf('26', plain,
% 0.58/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X0 @ X1)
% 0.58/0.77          | (r2_hidden @ X0 @ X2)
% 0.58/0.77          | ~ (r1_tarski @ X1 @ X2))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_tarski])).
% 0.58/0.77  thf('27', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.58/0.77          | ~ (r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.77  thf('28', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['6', '27'])).
% 0.58/0.77  thf('29', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i]:
% 0.58/0.77         (~ (r2_hidden @ X12 @ X13)
% 0.58/0.77          | (m1_subset_1 @ X12 @ X13)
% 0.58/0.77          | (v1_xboole_0 @ X13))),
% 0.58/0.77      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.58/0.77  thf(t7_boole, axiom,
% 0.58/0.77    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.58/0.77  thf('30', plain,
% 0.58/0.77      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.58/0.77      inference('cnf', [status(esa)], [t7_boole])).
% 0.58/0.77  thf('31', plain,
% 0.58/0.77      (![X12 : $i, X13 : $i]:
% 0.58/0.77         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.58/0.77      inference('clc', [status(thm)], ['29', '30'])).
% 0.58/0.77  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['28', '31'])).
% 0.58/0.77  thf('33', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.58/0.77          | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.58/0.77             (k3_subset_1 @ sk_A @ X0))
% 0.58/0.77          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.58/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.58/0.77  thf('34', plain,
% 0.58/0.77      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.58/0.77        | (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.58/0.77           (k3_subset_1 @ sk_A @ sk_B)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.77  thf('35', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('36', plain,
% 0.58/0.77      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.58/0.77      inference('demod', [status(thm)], ['34', '35'])).
% 0.58/0.77  thf('37', plain,
% 0.58/0.77      (![X0 : $i]:
% 0.58/0.77         ((r1_tarski @ sk_B @ X0)
% 0.58/0.77          | ~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0))),
% 0.58/0.77      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.77  thf('38', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.58/0.77      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.77  thf(t38_subset_1, axiom,
% 0.58/0.77    (![A:$i,B:$i]:
% 0.58/0.77     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.58/0.77       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.58/0.77         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.58/0.77  thf('39', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X25 @ (k3_subset_1 @ X24 @ X25))
% 0.58/0.77          | ((X25) = (k1_subset_1 @ X24))
% 0.58/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.58/0.77      inference('cnf', [status(esa)], [t38_subset_1])).
% 0.58/0.77  thf('40', plain, (![X15 : $i]: ((k1_subset_1 @ X15) = (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.58/0.77  thf('41', plain,
% 0.58/0.77      (![X24 : $i, X25 : $i]:
% 0.58/0.77         (~ (r1_tarski @ X25 @ (k3_subset_1 @ X24 @ X25))
% 0.58/0.77          | ((X25) = (k1_xboole_0))
% 0.58/0.77          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.58/0.77      inference('demod', [status(thm)], ['39', '40'])).
% 0.58/0.77  thf('42', plain,
% 0.58/0.77      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))
% 0.58/0.77        | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.77      inference('sup-', [status(thm)], ['38', '41'])).
% 0.58/0.77  thf('43', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.58/0.77      inference('sup-', [status(thm)], ['28', '31'])).
% 0.58/0.77  thf('44', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.58/0.77  thf('45', plain, (((sk_B) != (k1_xboole_0))),
% 0.58/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.77  thf('46', plain, ($false),
% 0.58/0.77      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.58/0.77  
% 0.58/0.77  % SZS output end Refutation
% 0.58/0.77  
% 0.58/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
