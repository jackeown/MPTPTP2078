%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u1EgKFPzSs

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:00 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 101 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :  283 ( 617 expanded)
%              Number of equality atoms :   36 (  77 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('0',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t18_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
     => ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X18 ) @ ( k3_tarski @ X19 ) )
      | ~ ( r1_setfam_1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t18_setfam_1])).

thf('2',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('4',plain,(
    r1_tarski @ ( k3_tarski @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('6',plain,
    ( ( k3_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_tarski @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k1_tarski @ X2 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X5 @ X6 ) )
      = ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X8 @ X7 ) @ X7 )
      | ( X7
        = ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('15',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_D @ X13 @ X14 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ X15 )
      | ~ ( r1_setfam_1 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X9 @ X11 ) @ X10 )
       != ( k2_tarski @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference(clc,[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_tarski @ X0 ) )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('27',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('28',plain,
    ( ( k3_tarski @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['13','25','26','27'])).

thf('29',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['6','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u1EgKFPzSs
% 0.16/0.37  % Computer   : n004.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 20:14:39 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.23/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.49  % Solved by: fo/fo7.sh
% 0.23/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.49  % done 27 iterations in 0.015s
% 0.23/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.49  % SZS output start Refutation
% 0.23/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.23/0.49  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.23/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.49  thf(t21_setfam_1, conjecture,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.49    (~( ![A:$i]:
% 0.23/0.49        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.23/0.49    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.23/0.49  thf('0', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(t18_setfam_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_setfam_1 @ A @ B ) =>
% 0.23/0.49       ( r1_tarski @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.23/0.49  thf('1', plain,
% 0.23/0.49      (![X18 : $i, X19 : $i]:
% 0.23/0.49         ((r1_tarski @ (k3_tarski @ X18) @ (k3_tarski @ X19))
% 0.23/0.49          | ~ (r1_setfam_1 @ X18 @ X19))),
% 0.23/0.49      inference('cnf', [status(esa)], [t18_setfam_1])).
% 0.23/0.49  thf('2', plain,
% 0.23/0.49      ((r1_tarski @ (k3_tarski @ sk_A) @ (k3_tarski @ k1_xboole_0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.23/0.49  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.23/0.49  thf('3', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.23/0.49  thf('4', plain, ((r1_tarski @ (k3_tarski @ sk_A) @ k1_xboole_0)),
% 0.23/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.23/0.49  thf(t3_xboole_1, axiom,
% 0.23/0.49    (![A:$i]:
% 0.23/0.49     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.49  thf('5', plain,
% 0.23/0.49      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.23/0.49  thf('6', plain, (((k3_tarski @ sk_A) = (k1_xboole_0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.49  thf(t41_enumset1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( k2_tarski @ A @ B ) =
% 0.23/0.49       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.23/0.49  thf('7', plain,
% 0.23/0.49      (![X2 : $i, X3 : $i]:
% 0.23/0.49         ((k2_tarski @ X2 @ X3)
% 0.23/0.49           = (k2_xboole_0 @ (k1_tarski @ X2) @ (k1_tarski @ X3)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.23/0.49  thf(t69_enumset1, axiom,
% 0.23/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.49  thf('8', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.49  thf(l51_zfmisc_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.49  thf('9', plain,
% 0.23/0.49      (![X5 : $i, X6 : $i]:
% 0.23/0.49         ((k3_tarski @ (k2_tarski @ X5 @ X6)) = (k2_xboole_0 @ X5 @ X6))),
% 0.23/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.49  thf('10', plain,
% 0.23/0.49      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.23/0.49  thf('11', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((k3_tarski @ (k1_tarski @ (k1_tarski @ X0))) = (k2_tarski @ X0 @ X0))),
% 0.23/0.49      inference('sup+', [status(thm)], ['7', '10'])).
% 0.23/0.49  thf('12', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.23/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.49  thf('13', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         ((k3_tarski @ (k1_tarski @ (k1_tarski @ X0))) = (k1_tarski @ X0))),
% 0.23/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.23/0.49  thf(t41_zfmisc_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.49          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.23/0.49  thf('14', plain,
% 0.23/0.49      (![X7 : $i, X8 : $i]:
% 0.23/0.49         (((X7) = (k1_xboole_0))
% 0.23/0.49          | (r2_hidden @ (sk_C @ X8 @ X7) @ X7)
% 0.23/0.49          | ((X7) = (k1_tarski @ X8)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.23/0.49  thf('15', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf(d2_setfam_1, axiom,
% 0.23/0.49    (![A:$i,B:$i]:
% 0.23/0.49     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.23/0.49       ( ![C:$i]:
% 0.23/0.49         ( ~( ( r2_hidden @ C @ A ) & 
% 0.23/0.49              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.23/0.49  thf('16', plain,
% 0.23/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.49         ((r2_hidden @ (sk_D @ X13 @ X14) @ X14)
% 0.23/0.49          | ~ (r2_hidden @ X13 @ X15)
% 0.23/0.49          | ~ (r1_setfam_1 @ X15 @ X14))),
% 0.23/0.49      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.23/0.49  thf('17', plain,
% 0.23/0.49      (![X0 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X0 @ sk_A)
% 0.23/0.49          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.49  thf(t3_boole, axiom,
% 0.23/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.23/0.49  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.23/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.23/0.49  thf(t72_zfmisc_1, axiom,
% 0.23/0.49    (![A:$i,B:$i,C:$i]:
% 0.23/0.49     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.23/0.49       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.23/0.49  thf('19', plain,
% 0.23/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.49         (~ (r2_hidden @ X9 @ X10)
% 0.23/0.49          | ((k4_xboole_0 @ (k2_tarski @ X9 @ X11) @ X10)
% 0.23/0.49              != (k2_tarski @ X9 @ X11)))),
% 0.23/0.49      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.23/0.49  thf('20', plain,
% 0.23/0.49      (![X0 : $i, X1 : $i]:
% 0.23/0.49         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.23/0.49          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.23/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.23/0.49  thf('21', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.23/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.23/0.49  thf('22', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.23/0.49      inference('clc', [status(thm)], ['17', '21'])).
% 0.23/0.49  thf('23', plain,
% 0.23/0.49      (![X0 : $i]: (((sk_A) = (k1_tarski @ X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.23/0.49      inference('sup-', [status(thm)], ['14', '22'])).
% 0.23/0.49  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('25', plain, (![X0 : $i]: ((sk_A) = (k1_tarski @ X0))),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.23/0.49  thf('26', plain, (![X0 : $i]: ((sk_A) = (k1_tarski @ X0))),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.23/0.49  thf('27', plain, (![X0 : $i]: ((sk_A) = (k1_tarski @ X0))),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.23/0.49  thf('28', plain, (((k3_tarski @ sk_A) = (sk_A))),
% 0.23/0.49      inference('demod', [status(thm)], ['13', '25', '26', '27'])).
% 0.23/0.49  thf('29', plain, (((k1_xboole_0) = (sk_A))),
% 0.23/0.49      inference('sup+', [status(thm)], ['6', '28'])).
% 0.23/0.49  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.49  thf('31', plain, ($false),
% 0.23/0.49      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.23/0.49  
% 0.23/0.49  % SZS output end Refutation
% 0.23/0.49  
% 0.23/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
