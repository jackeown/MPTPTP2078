%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7vQUeBdoyp

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   14
%              Number of atoms          :  393 ( 625 expanded)
%              Number of equality atoms :   39 (  78 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t139_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i,C: $i,D: $i] :
          ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
            | ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) )
         => ( r1_tarski @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X7 ) @ ( k2_zfmisc_1 @ X10 @ X9 ) )
      | ( r1_tarski @ X8 @ X10 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t139_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( X1
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t195_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = A )
              & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
                = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t195_relat_1])).

thf('9',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_A )
   <= ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( r1_tarski @ X17 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X17 ) @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X7 @ X8 ) @ ( k2_zfmisc_1 @ X9 @ X10 ) )
      | ( r1_tarski @ X8 @ X10 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t139_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('16',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) @ X16 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(split,[status(esa)],['9'])).

thf('21',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    = sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_A )
    | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(split,[status(esa)],['9'])).

thf('30',plain,(
    ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['10','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('35',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7vQUeBdoyp
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:55:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 38 iterations in 0.020s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(t21_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( r1_tarski @
% 0.22/0.49         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (![X17 : $i]:
% 0.22/0.49         ((r1_tarski @ X17 @ 
% 0.22/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.22/0.49          | ~ (v1_relat_1 @ X17))),
% 0.22/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.49  thf(t139_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.49       ( ![B:$i,C:$i,D:$i]:
% 0.22/0.49         ( ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) | 
% 0.22/0.49             ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ D @ C ) ) ) =>
% 0.22/0.49           ( r1_tarski @ B @ D ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_zfmisc_1 @ X8 @ X7) @ (k2_zfmisc_1 @ X10 @ X9))
% 0.22/0.49          | (r1_tarski @ X8 @ X10)
% 0.22/0.49          | (v1_xboole_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t139_zfmisc_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.49          | (v1_xboole_0 @ X0)
% 0.22/0.49          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf(fc6_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0)
% 0.22/0.49          | (r1_tarski @ X1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf(t193_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i]:
% 0.22/0.49         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 0.22/0.49      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.22/0.49  thf(d10_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X4 : $i, X6 : $i]:
% 0.22/0.49         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.22/0.49          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X0) | ((X1) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.49  thf(t195_relat_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.22/0.49               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49             ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.22/0.49                  ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t195_relat_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) != (sk_A))
% 0.22/0.49        | ((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) != (sk_B_2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      ((((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) != (sk_A)))
% 0.22/0.49         <= (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_A))))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X17 : $i]:
% 0.22/0.49         ((r1_tarski @ X17 @ 
% 0.22/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X17) @ (k2_relat_1 @ X17)))
% 0.22/0.49          | ~ (v1_relat_1 @ X17))),
% 0.22/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_zfmisc_1 @ X7 @ X8) @ (k2_zfmisc_1 @ X9 @ X10))
% 0.22/0.49          | (r1_tarski @ X8 @ X10)
% 0.22/0.49          | (v1_xboole_0 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [t139_zfmisc_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.49          | (v1_xboole_0 @ X1)
% 0.22/0.49          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X1)
% 0.22/0.49          | (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.22/0.49  thf(t194_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i]:
% 0.22/0.49         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) @ X16)),
% 0.22/0.49      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X4 : $i, X6 : $i]:
% 0.22/0.49         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.22/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.22/0.49          | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v1_xboole_0 @ X1) | ((X0) = (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) != (sk_B_2)))
% 0.22/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_B_2))))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      (((((sk_B_2) != (sk_B_2)) | (v1_xboole_0 @ sk_A)))
% 0.22/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_B_2))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((v1_xboole_0 @ sk_A))
% 0.22/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_B_2))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.49  thf(t7_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.49  thf(d1_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.49         <= (~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_B_2))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.49  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_B_2)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_A))) | 
% 0.22/0.49       ~ (((k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_B_2)))),
% 0.22/0.49      inference('split', [status(esa)], ['9'])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (~ (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) = (sk_A)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, (((k1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)) != (sk_A))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['10', '30'])).
% 0.22/0.49  thf('32', plain, ((((sk_A) != (sk_A)) | (v1_xboole_0 @ sk_B_2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '31'])).
% 0.22/0.49  thf('33', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.22/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.49  thf('35', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
