%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HiUzN7DeHx

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:03 EST 2020

% Result     : Theorem 3.85s
% Output     : Refutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 133 expanded)
%              Number of leaves         :   18 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  414 ( 967 expanded)
%              Number of equality atoms :    9 (  44 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k3_relat_1 @ X28 ) @ ( k3_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('30',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k3_relat_1 @ X28 ) @ ( k3_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ( r1_tarski @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','35'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['38','39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HiUzN7DeHx
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:16:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.85/4.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.85/4.07  % Solved by: fo/fo7.sh
% 3.85/4.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.85/4.07  % done 4521 iterations in 3.605s
% 3.85/4.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.85/4.07  % SZS output start Refutation
% 3.85/4.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.85/4.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.85/4.07  thf(sk_A_type, type, sk_A: $i).
% 3.85/4.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.85/4.07  thf(sk_B_type, type, sk_B: $i).
% 3.85/4.07  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 3.85/4.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.85/4.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.85/4.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.85/4.07  thf(d10_xboole_0, axiom,
% 3.85/4.07    (![A:$i,B:$i]:
% 3.85/4.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.85/4.07  thf('0', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.85/4.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.85/4.07  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.85/4.07      inference('simplify', [status(thm)], ['0'])).
% 3.85/4.07  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.85/4.07      inference('simplify', [status(thm)], ['0'])).
% 3.85/4.07  thf(t19_xboole_1, axiom,
% 3.85/4.07    (![A:$i,B:$i,C:$i]:
% 3.85/4.07     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 3.85/4.07       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 3.85/4.07  thf('3', plain,
% 3.85/4.07      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.85/4.07         (~ (r1_tarski @ X5 @ X6)
% 3.85/4.07          | ~ (r1_tarski @ X5 @ X7)
% 3.85/4.07          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 3.85/4.07      inference('cnf', [status(esa)], [t19_xboole_1])).
% 3.85/4.07  thf('4', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         ((r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X0 @ X1))),
% 3.85/4.07      inference('sup-', [status(thm)], ['2', '3'])).
% 3.85/4.07  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X0))),
% 3.85/4.07      inference('sup-', [status(thm)], ['1', '4'])).
% 3.85/4.07  thf(t17_xboole_1, axiom,
% 3.85/4.07    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 3.85/4.07  thf('6', plain,
% 3.85/4.07      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 3.85/4.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.85/4.07  thf('7', plain,
% 3.85/4.07      (![X0 : $i, X2 : $i]:
% 3.85/4.07         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.85/4.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.85/4.07  thf('8', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 3.85/4.07          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 3.85/4.07      inference('sup-', [status(thm)], ['6', '7'])).
% 3.85/4.07  thf('9', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 3.85/4.07      inference('sup-', [status(thm)], ['5', '8'])).
% 3.85/4.07  thf(t22_xboole_1, axiom,
% 3.85/4.07    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.85/4.07  thf('10', plain,
% 3.85/4.07      (![X8 : $i, X9 : $i]:
% 3.85/4.07         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 3.85/4.07      inference('cnf', [status(esa)], [t22_xboole_1])).
% 3.85/4.07  thf('11', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.85/4.07      inference('sup+', [status(thm)], ['9', '10'])).
% 3.85/4.07  thf(t31_xboole_1, axiom,
% 3.85/4.07    (![A:$i,B:$i,C:$i]:
% 3.85/4.07     ( r1_tarski @
% 3.85/4.07       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 3.85/4.07       ( k2_xboole_0 @ B @ C ) ))).
% 3.85/4.07  thf('12', plain,
% 3.85/4.07      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.85/4.07         (r1_tarski @ 
% 3.85/4.07          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 3.85/4.07          (k2_xboole_0 @ X11 @ X12))),
% 3.85/4.07      inference('cnf', [status(esa)], [t31_xboole_1])).
% 3.85/4.07  thf('13', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (r1_tarski @ 
% 3.85/4.07          (k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.85/4.07          X0)),
% 3.85/4.07      inference('sup+', [status(thm)], ['11', '12'])).
% 3.85/4.07  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.85/4.07      inference('sup+', [status(thm)], ['9', '10'])).
% 3.85/4.07  thf('15', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.85/4.07      inference('demod', [status(thm)], ['13', '14'])).
% 3.85/4.07  thf(t31_relat_1, axiom,
% 3.85/4.07    (![A:$i]:
% 3.85/4.07     ( ( v1_relat_1 @ A ) =>
% 3.85/4.07       ( ![B:$i]:
% 3.85/4.07         ( ( v1_relat_1 @ B ) =>
% 3.85/4.07           ( ( r1_tarski @ A @ B ) =>
% 3.85/4.07             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 3.85/4.07  thf('16', plain,
% 3.85/4.07      (![X27 : $i, X28 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X27)
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ X28) @ (k3_relat_1 @ X27))
% 3.85/4.07          | ~ (r1_tarski @ X28 @ X27)
% 3.85/4.07          | ~ (v1_relat_1 @ X28))),
% 3.85/4.07      inference('cnf', [status(esa)], [t31_relat_1])).
% 3.85/4.07  thf('17', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.85/4.07             (k3_relat_1 @ X0))
% 3.85/4.07          | ~ (v1_relat_1 @ X0))),
% 3.85/4.07      inference('sup-', [status(thm)], ['15', '16'])).
% 3.85/4.07  thf('18', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.85/4.07      inference('demod', [status(thm)], ['13', '14'])).
% 3.85/4.07  thf(t3_subset, axiom,
% 3.85/4.07    (![A:$i,B:$i]:
% 3.85/4.07     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.85/4.07  thf('19', plain,
% 3.85/4.07      (![X22 : $i, X24 : $i]:
% 3.85/4.07         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 3.85/4.07      inference('cnf', [status(esa)], [t3_subset])).
% 3.85/4.07  thf('20', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 3.85/4.07      inference('sup-', [status(thm)], ['18', '19'])).
% 3.85/4.07  thf(cc2_relat_1, axiom,
% 3.85/4.07    (![A:$i]:
% 3.85/4.07     ( ( v1_relat_1 @ A ) =>
% 3.85/4.07       ( ![B:$i]:
% 3.85/4.07         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.85/4.07  thf('21', plain,
% 3.85/4.07      (![X25 : $i, X26 : $i]:
% 3.85/4.07         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 3.85/4.07          | (v1_relat_1 @ X25)
% 3.85/4.07          | ~ (v1_relat_1 @ X26))),
% 3.85/4.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.85/4.07  thf('22', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.85/4.07      inference('sup-', [status(thm)], ['20', '21'])).
% 3.85/4.07  thf('23', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X0)
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.85/4.07             (k3_relat_1 @ X0)))),
% 3.85/4.07      inference('clc', [status(thm)], ['17', '22'])).
% 3.85/4.07  thf('24', plain,
% 3.85/4.07      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 3.85/4.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.85/4.07  thf('25', plain,
% 3.85/4.07      (![X22 : $i, X24 : $i]:
% 3.85/4.07         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 3.85/4.07      inference('cnf', [status(esa)], [t3_subset])).
% 3.85/4.07  thf('26', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 3.85/4.07      inference('sup-', [status(thm)], ['24', '25'])).
% 3.85/4.07  thf('27', plain,
% 3.85/4.07      (![X25 : $i, X26 : $i]:
% 3.85/4.07         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 3.85/4.07          | (v1_relat_1 @ X25)
% 3.85/4.07          | ~ (v1_relat_1 @ X26))),
% 3.85/4.07      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.85/4.07  thf('28', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.85/4.07      inference('sup-', [status(thm)], ['26', '27'])).
% 3.85/4.07  thf('29', plain,
% 3.85/4.07      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 3.85/4.07      inference('cnf', [status(esa)], [t17_xboole_1])).
% 3.85/4.07  thf('30', plain,
% 3.85/4.07      (![X27 : $i, X28 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X27)
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ X28) @ (k3_relat_1 @ X27))
% 3.85/4.07          | ~ (r1_tarski @ X28 @ X27)
% 3.85/4.07          | ~ (v1_relat_1 @ X28))),
% 3.85/4.07      inference('cnf', [status(esa)], [t31_relat_1])).
% 3.85/4.07  thf('31', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 3.85/4.07             (k3_relat_1 @ X0))
% 3.85/4.07          | ~ (v1_relat_1 @ X0))),
% 3.85/4.07      inference('sup-', [status(thm)], ['29', '30'])).
% 3.85/4.07  thf('32', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X1)
% 3.85/4.07          | ~ (v1_relat_1 @ X1)
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.85/4.07             (k3_relat_1 @ X1)))),
% 3.85/4.07      inference('sup-', [status(thm)], ['28', '31'])).
% 3.85/4.07  thf('33', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         ((r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.85/4.07           (k3_relat_1 @ X1))
% 3.85/4.07          | ~ (v1_relat_1 @ X1))),
% 3.85/4.07      inference('simplify', [status(thm)], ['32'])).
% 3.85/4.07  thf('34', plain,
% 3.85/4.07      (![X5 : $i, X6 : $i, X7 : $i]:
% 3.85/4.07         (~ (r1_tarski @ X5 @ X6)
% 3.85/4.07          | ~ (r1_tarski @ X5 @ X7)
% 3.85/4.07          | (r1_tarski @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 3.85/4.07      inference('cnf', [status(esa)], [t19_xboole_1])).
% 3.85/4.07  thf('35', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X0)
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 3.85/4.07             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 3.85/4.07          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 3.85/4.07      inference('sup-', [status(thm)], ['33', '34'])).
% 3.85/4.07  thf('36', plain,
% 3.85/4.07      (![X0 : $i, X1 : $i]:
% 3.85/4.07         (~ (v1_relat_1 @ X0)
% 3.85/4.07          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 3.85/4.07             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 3.85/4.07          | ~ (v1_relat_1 @ X1))),
% 3.85/4.07      inference('sup-', [status(thm)], ['23', '35'])).
% 3.85/4.07  thf(t34_relat_1, conjecture,
% 3.85/4.07    (![A:$i]:
% 3.85/4.07     ( ( v1_relat_1 @ A ) =>
% 3.85/4.07       ( ![B:$i]:
% 3.85/4.07         ( ( v1_relat_1 @ B ) =>
% 3.85/4.07           ( r1_tarski @
% 3.85/4.07             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 3.85/4.07             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 3.85/4.07  thf(zf_stmt_0, negated_conjecture,
% 3.85/4.07    (~( ![A:$i]:
% 3.85/4.07        ( ( v1_relat_1 @ A ) =>
% 3.85/4.07          ( ![B:$i]:
% 3.85/4.07            ( ( v1_relat_1 @ B ) =>
% 3.85/4.07              ( r1_tarski @
% 3.85/4.07                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 3.85/4.07                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 3.85/4.07    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 3.85/4.07  thf('37', plain,
% 3.85/4.07      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 3.85/4.07          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 3.85/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.85/4.07  thf('38', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 3.85/4.07      inference('sup-', [status(thm)], ['36', '37'])).
% 3.85/4.07  thf('39', plain, ((v1_relat_1 @ sk_A)),
% 3.85/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.85/4.07  thf('40', plain, ((v1_relat_1 @ sk_B)),
% 3.85/4.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.85/4.07  thf('41', plain, ($false),
% 3.85/4.07      inference('demod', [status(thm)], ['38', '39', '40'])).
% 3.85/4.07  
% 3.85/4.07  % SZS output end Refutation
% 3.85/4.07  
% 3.93/4.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
