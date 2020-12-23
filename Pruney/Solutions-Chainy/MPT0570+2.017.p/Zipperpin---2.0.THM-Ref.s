%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h3JVLNy5vk

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  65 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  292 ( 376 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t174_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ~ ( ( A != k1_xboole_0 )
            & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
            & ( ( k10_relat_1 @ B @ A )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t174_relat_1])).

thf('0',plain,
    ( ( k10_relat_1 @ sk_B_1 @ sk_A )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k10_relat_1 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('2',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_B_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_xboole_0 @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('11',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['11','13'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('18',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r1_tarski @ X19 @ X17 )
      | ( X18
       != ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r1_tarski @ X19 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup-',[status(thm)],['14','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h3JVLNy5vk
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 70 iterations in 0.035s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t174_relat_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.20/0.49            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ B ) =>
% 0.20/0.49          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49               ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.20/0.49               ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t174_relat_1])).
% 0.20/0.49  thf('0', plain, (((k10_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t173_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.49         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X28 @ X29) != (k1_xboole_0))
% 0.20/0.49          | (r1_xboole_0 @ (k2_relat_1 @ X28) @ X29)
% 0.20/0.49          | ~ (v1_relat_1 @ X28))),
% 0.20/0.49      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.49        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf('3', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49        | (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ sk_A)),
% 0.20/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.49  thf('6', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t63_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.49       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X11 @ X12)
% 0.20/0.49          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.20/0.49          | (r1_xboole_0 @ X11 @ X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ sk_A @ X0)
% 0.20/0.49          | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_B_1) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain, ((r1_xboole_0 @ sk_A @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.49  thf(t69_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.49       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X14 @ X15)
% 0.20/0.49          | ~ (r1_tarski @ X14 @ X15)
% 0.20/0.49          | (v1_xboole_0 @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.49  thf('11', plain, (((v1_xboole_0 @ sk_A) | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf(d10_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.49  thf('13', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.20/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.49  thf('14', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '13'])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X22 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X22))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X23 : $i, X24 : $i]:
% 0.20/0.49         ((r2_hidden @ X23 @ X24)
% 0.20/0.49          | (v1_xboole_0 @ X24)
% 0.20/0.49          | ~ (m1_subset_1 @ X23 @ X24))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.20/0.49          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf(fc1_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.49  thf('18', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.20/0.49      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf(d1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X19 @ X18)
% 0.20/0.49          | (r1_tarski @ X19 @ X17)
% 0.20/0.49          | ((X18) != (k1_zfmisc_1 @ X17)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X17 : $i, X19 : $i]:
% 0.20/0.49         ((r1_tarski @ X19 @ X17) | ~ (r2_hidden @ X19 @ (k1_zfmisc_1 @ X17)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.49  thf(d8_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.20/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i]:
% 0.20/0.49         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf(t6_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.49  thf('29', plain, (((k1_xboole_0) = (sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '28'])).
% 0.20/0.49  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('31', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
