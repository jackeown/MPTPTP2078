%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dr5y2kner4

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:43 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 188 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  493 (1436 expanded)
%              Number of equality atoms :   29 (  69 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( r1_tarski @ X9 @ X7 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r2_hidden @ X6 @ X8 )
      | ( X8
       != ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( m1_subset_1 @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ X11 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('20',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t39_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B )
      <=> ( B
          = ( k2_subset_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X26 @ X27 ) @ X27 )
      | ( X27
        = ( k2_subset_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t39_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('23',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X26 @ X27 ) @ X27 )
      | ( X27 = X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k3_subset_1 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('28',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( ( k3_subset_1 @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( r1_tarski @ X23 @ ( k3_subset_1 @ X24 @ X25 ) )
      | ~ ( r1_tarski @ X25 @ ( k3_subset_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('36',plain,(
    r1_tarski @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['29','38'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X16 ) @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('41',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('42',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X21 @ ( k3_subset_1 @ X21 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ( k2_subset_1 @ X22 )
      = ( k3_subset_1 @ X22 @ ( k1_subset_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf('46',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = X15 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('47',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('48',plain,(
    ! [X22: $i] :
      ( X22
      = ( k3_subset_1 @ X22 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','48'])).

thf('50',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['20','39','49'])).

thf('51',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Dr5y2kner4
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:35:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.72  % Solved by: fo/fo7.sh
% 0.50/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.72  % done 552 iterations in 0.265s
% 0.50/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.72  % SZS output start Refutation
% 0.50/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.72  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.50/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.72  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.50/0.72  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.50/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.50/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.50/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.72  thf(t40_subset_1, conjecture,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.50/0.72         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.50/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.72    (~( ![A:$i,B:$i,C:$i]:
% 0.50/0.72        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72          ( ( ( r1_tarski @ B @ C ) & 
% 0.50/0.72              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.50/0.72            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.50/0.72    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.50/0.72  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(d2_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( v1_xboole_0 @ A ) =>
% 0.50/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.50/0.72       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.50/0.72         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.72  thf('1', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X11 @ X12)
% 0.50/0.72          | (r2_hidden @ X11 @ X12)
% 0.50/0.72          | (v1_xboole_0 @ X12))),
% 0.50/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.72  thf('2', plain,
% 0.50/0.72      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.72        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['0', '1'])).
% 0.50/0.72  thf(fc1_subset_1, axiom,
% 0.50/0.72    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.72  thf('3', plain, (![X19 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X19))),
% 0.50/0.72      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.50/0.72  thf('4', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('clc', [status(thm)], ['2', '3'])).
% 0.50/0.72  thf(d1_zfmisc_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.50/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.50/0.72  thf('5', plain,
% 0.50/0.72      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X9 @ X8)
% 0.50/0.72          | (r1_tarski @ X9 @ X7)
% 0.50/0.72          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.50/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.72  thf('6', plain,
% 0.50/0.72      (![X7 : $i, X9 : $i]:
% 0.50/0.72         ((r1_tarski @ X9 @ X7) | ~ (r2_hidden @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.50/0.72      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.72  thf('7', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.50/0.72      inference('sup-', [status(thm)], ['4', '6'])).
% 0.50/0.72  thf('8', plain, ((r1_tarski @ sk_B_1 @ sk_C_1)),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t1_xboole_1, axiom,
% 0.50/0.72    (![A:$i,B:$i,C:$i]:
% 0.50/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.50/0.72       ( r1_tarski @ A @ C ) ))).
% 0.50/0.72  thf('9', plain,
% 0.50/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.72         (~ (r1_tarski @ X3 @ X4)
% 0.50/0.72          | ~ (r1_tarski @ X4 @ X5)
% 0.50/0.72          | (r1_tarski @ X3 @ X5))),
% 0.50/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.50/0.72  thf('10', plain,
% 0.50/0.72      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.72  thf('11', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.50/0.72      inference('sup-', [status(thm)], ['7', '10'])).
% 0.50/0.72  thf('12', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.50/0.72         (~ (r1_tarski @ X6 @ X7)
% 0.50/0.72          | (r2_hidden @ X6 @ X8)
% 0.50/0.72          | ((X8) != (k1_zfmisc_1 @ X7)))),
% 0.50/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.50/0.72  thf('13', plain,
% 0.50/0.72      (![X6 : $i, X7 : $i]:
% 0.50/0.72         ((r2_hidden @ X6 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X6 @ X7))),
% 0.50/0.72      inference('simplify', [status(thm)], ['12'])).
% 0.50/0.72  thf('14', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['11', '13'])).
% 0.50/0.72  thf('15', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         (~ (r2_hidden @ X11 @ X12)
% 0.50/0.72          | (m1_subset_1 @ X11 @ X12)
% 0.50/0.72          | (v1_xboole_0 @ X12))),
% 0.50/0.72      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.50/0.72  thf(d1_xboole_0, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.50/0.72  thf('16', plain,
% 0.50/0.72      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.50/0.72      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.50/0.72  thf('17', plain,
% 0.50/0.72      (![X11 : $i, X12 : $i]:
% 0.50/0.72         ((m1_subset_1 @ X11 @ X12) | ~ (r2_hidden @ X11 @ X12))),
% 0.50/0.72      inference('clc', [status(thm)], ['15', '16'])).
% 0.50/0.72  thf('18', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['14', '17'])).
% 0.50/0.72  thf(involutiveness_k3_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.50/0.72  thf('19', plain,
% 0.50/0.72      (![X20 : $i, X21 : $i]:
% 0.50/0.72         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.50/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.50/0.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.72  thf('20', plain,
% 0.50/0.72      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.72  thf('21', plain,
% 0.50/0.72      (((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['18', '19'])).
% 0.50/0.72  thf(t39_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ B ) <=>
% 0.50/0.72         ( ( B ) = ( k2_subset_1 @ A ) ) ) ))).
% 0.50/0.72  thf('22', plain,
% 0.50/0.72      (![X26 : $i, X27 : $i]:
% 0.50/0.72         (~ (r1_tarski @ (k3_subset_1 @ X26 @ X27) @ X27)
% 0.50/0.72          | ((X27) = (k2_subset_1 @ X26))
% 0.50/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t39_subset_1])).
% 0.50/0.72  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.50/0.72  thf('23', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 0.50/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.50/0.72  thf('24', plain,
% 0.50/0.72      (![X26 : $i, X27 : $i]:
% 0.50/0.72         (~ (r1_tarski @ (k3_subset_1 @ X26 @ X27) @ X27)
% 0.50/0.72          | ((X27) = (X26))
% 0.50/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 0.50/0.72      inference('demod', [status(thm)], ['22', '23'])).
% 0.50/0.72  thf('25', plain,
% 0.50/0.72      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.50/0.72        | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.72        | ((k3_subset_1 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['21', '24'])).
% 0.50/0.72  thf('26', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['14', '17'])).
% 0.50/0.72  thf(dt_k3_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.50/0.72  thf('27', plain,
% 0.50/0.72      (![X17 : $i, X18 : $i]:
% 0.50/0.72         ((m1_subset_1 @ (k3_subset_1 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.50/0.72          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.50/0.72  thf('28', plain,
% 0.50/0.72      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.72  thf('29', plain,
% 0.50/0.72      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.50/0.72        | ((k3_subset_1 @ sk_A @ sk_B_1) = (sk_A)))),
% 0.50/0.72      inference('demod', [status(thm)], ['25', '28'])).
% 0.50/0.72  thf('30', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('31', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf(t35_subset_1, axiom,
% 0.50/0.72    (![A:$i,B:$i]:
% 0.50/0.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72       ( ![C:$i]:
% 0.50/0.72         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.72           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.50/0.72             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.50/0.72  thf('32', plain,
% 0.50/0.72      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 0.50/0.72          | (r1_tarski @ X23 @ (k3_subset_1 @ X24 @ X25))
% 0.50/0.72          | ~ (r1_tarski @ X25 @ (k3_subset_1 @ X24 @ X23))
% 0.50/0.72          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.50/0.72  thf('33', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.50/0.72          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.50/0.72          | (r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ X0)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.72  thf('34', plain,
% 0.50/0.72      (((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.50/0.72        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.50/0.72      inference('sup-', [status(thm)], ['30', '33'])).
% 0.50/0.72  thf('35', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.50/0.72      inference('sup-', [status(thm)], ['14', '17'])).
% 0.50/0.72  thf('36', plain, ((r1_tarski @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.50/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.50/0.72  thf('37', plain,
% 0.50/0.72      (![X0 : $i]: ((r1_tarski @ sk_B_1 @ X0) | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.72  thf('38', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.50/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.72  thf('39', plain, (((k3_subset_1 @ sk_A @ sk_B_1) = (sk_A))),
% 0.50/0.72      inference('demod', [status(thm)], ['29', '38'])).
% 0.50/0.72  thf(dt_k1_subset_1, axiom,
% 0.50/0.72    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.50/0.72  thf('40', plain,
% 0.50/0.72      (![X16 : $i]: (m1_subset_1 @ (k1_subset_1 @ X16) @ (k1_zfmisc_1 @ X16))),
% 0.50/0.72      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.50/0.72  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.50/0.72  thf('41', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.50/0.72  thf('42', plain,
% 0.50/0.72      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.50/0.72      inference('demod', [status(thm)], ['40', '41'])).
% 0.50/0.72  thf('43', plain,
% 0.50/0.72      (![X20 : $i, X21 : $i]:
% 0.50/0.72         (((k3_subset_1 @ X21 @ (k3_subset_1 @ X21 @ X20)) = (X20))
% 0.50/0.72          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 0.50/0.72      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.50/0.72  thf('44', plain,
% 0.50/0.72      (![X0 : $i]:
% 0.50/0.72         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.50/0.72      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.72  thf(t22_subset_1, axiom,
% 0.50/0.72    (![A:$i]:
% 0.50/0.72     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.50/0.72  thf('45', plain,
% 0.50/0.72      (![X22 : $i]:
% 0.50/0.72         ((k2_subset_1 @ X22) = (k3_subset_1 @ X22 @ (k1_subset_1 @ X22)))),
% 0.50/0.72      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.50/0.72  thf('46', plain, (![X15 : $i]: ((k2_subset_1 @ X15) = (X15))),
% 0.50/0.72      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.50/0.72  thf('47', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.50/0.72      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.50/0.72  thf('48', plain, (![X22 : $i]: ((X22) = (k3_subset_1 @ X22 @ k1_xboole_0))),
% 0.50/0.72      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.50/0.72  thf('49', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.50/0.72      inference('demod', [status(thm)], ['44', '48'])).
% 0.50/0.72  thf('50', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.50/0.72      inference('demod', [status(thm)], ['20', '39', '49'])).
% 0.50/0.72  thf('51', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.50/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.72  thf('52', plain, ($false),
% 0.50/0.72      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.50/0.72  
% 0.50/0.72  % SZS output end Refutation
% 0.50/0.72  
% 0.50/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
