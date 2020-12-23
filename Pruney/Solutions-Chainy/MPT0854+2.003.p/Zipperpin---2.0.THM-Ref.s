%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.86rrKvPoVq

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   48 (  87 expanded)
%              Number of leaves         :   16 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  316 ( 715 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t10_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
       => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_mcart_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k4_tarski @ ( sk_C @ X5 ) @ ( sk_D @ X5 ) ) )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_A
      = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('7',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t8_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) )
        = A ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k4_tarski @ ( k1_mcart_1 @ X12 ) @ ( k2_mcart_1 @ X12 ) )
        = X12 )
      | ( X12
       != ( k4_tarski @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t8_mcart_1])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_tarski @ ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) ) @ ( k2_mcart_1 @ ( k4_tarski @ X13 @ X14 ) ) )
      = ( k4_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_tarski @ ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) ) @ ( k2_mcart_1 @ ( k4_tarski @ X13 @ X14 ) ) )
      = ( k4_tarski @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X3 @ X2 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_C @ sk_A ) @ ( sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['20','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.86rrKvPoVq
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 57 iterations in 0.043s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i).
% 0.22/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i > $i).
% 0.22/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(t10_mcart_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.50        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.50          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.50            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t10_mcart_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)
% 0.22/0.50        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))
% 0.22/0.50         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d1_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) <=>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.50              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X5 : $i, X6 : $i]:
% 0.22/0.50         (((X5) = (k4_tarski @ (sk_C @ X5) @ (sk_D @ X5)))
% 0.22/0.50          | ~ (r2_hidden @ X5 @ X6)
% 0.22/0.50          | ~ (v1_relat_1 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.22/0.50        | ((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf(fc6_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('7', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(t8_mcart_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.22/0.50       ( ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.50         (((k4_tarski @ (k1_mcart_1 @ X12) @ (k2_mcart_1 @ X12)) = (X12))
% 0.22/0.50          | ((X12) != (k4_tarski @ X13 @ X14)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t8_mcart_1])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k4_tarski @ (k1_mcart_1 @ (k4_tarski @ X13 @ X14)) @ 
% 0.22/0.50           (k2_mcart_1 @ (k4_tarski @ X13 @ X14))) = (k4_tarski @ X13 @ X14))),
% 0.22/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  thf(t106_zfmisc_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.22/0.50       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ X1)
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ X3 @ X2))
% 0.22/0.50          | (r2_hidden @ (k1_mcart_1 @ (k4_tarski @ X1 @ X0)) @ X3))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k1_mcart_1 @ (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A))) @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '11'])).
% 0.22/0.50  thf('13', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.50          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.50  thf('15', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))
% 0.22/0.50         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1)))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('17', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)) | 
% 0.22/0.50       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B_1))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('19', plain, (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, (~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['1', '19'])).
% 0.22/0.50  thf('21', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('22', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         ((k4_tarski @ (k1_mcart_1 @ (k4_tarski @ X13 @ X14)) @ 
% 0.22/0.50           (k2_mcart_1 @ (k4_tarski @ X13 @ X14))) = (k4_tarski @ X13 @ X14))),
% 0.22/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         ((r2_hidden @ X2 @ X3)
% 0.22/0.50          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ X3 @ X2))
% 0.22/0.50          | (r2_hidden @ (k2_mcart_1 @ (k4_tarski @ X1 @ X0)) @ X2))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k2_mcart_1 @ (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A))) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['22', '25'])).
% 0.22/0.50  thf('27', plain, (((sk_A) = (k4_tarski @ (sk_C @ sk_A) @ (sk_D @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.50          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '28'])).
% 0.22/0.50  thf('30', plain, ($false), inference('demod', [status(thm)], ['20', '29'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
