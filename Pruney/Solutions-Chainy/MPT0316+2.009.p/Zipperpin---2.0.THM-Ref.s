%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MJjxFf8uBq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 (  86 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :  464 ( 872 expanded)
%              Number of equality atoms :   35 (  66 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t128_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
    <=> ( ( A = C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) )
      <=> ( ( A = C )
          & ( r2_hidden @ B @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t128_zfmisc_1])).

thf('0',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k1_enumset1 @ X6 @ X6 @ X7 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('9',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('18',plain,(
    ! [X26: $i] :
      ( ( k2_tarski @ X26 @ X26 )
      = ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('20',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X31 ) )
      | ~ ( r2_hidden @ X29 @ X31 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('29',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D_1 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A != sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['22'])).

thf('32',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ X29 @ X30 )
      | ~ ( r2_hidden @ ( k4_tarski @ X27 @ X29 ) @ ( k2_zfmisc_1 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('34',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('36',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','17','30','31','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MJjxFf8uBq
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 60 iterations in 0.026s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.48  thf(t128_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @
% 0.20/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.48       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48        ( ( r2_hidden @
% 0.20/0.48            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.20/0.48          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((((sk_A) = (sk_C))
% 0.20/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((((sk_A) = (sk_C))) | 
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf(l54_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.48         ((r2_hidden @ X27 @ X28)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X30)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf(t76_enumset1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X26 : $i]: ((k1_enumset1 @ X26 @ X26 @ X26) = (k1_tarski @ X26))),
% 0.20/0.48      inference('cnf', [status(esa)], [t76_enumset1])).
% 0.20/0.48  thf(t70_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k1_enumset1 @ X6 @ X6 @ X7) = (k2_tarski @ X6 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.48  thf('7', plain, (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf(d2_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.20/0.48          | ((X4) = (X3))
% 0.20/0.48          | ((X4) = (X0))
% 0.20/0.48          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (((X4) = (X0))
% 0.20/0.48          | ((X4) = (X3))
% 0.20/0.48          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      ((((sk_A) = (sk_C)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_D_1)
% 0.20/0.48        | ((sk_A) != (sk_C))
% 0.20/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      ((((sk_A) != (sk_A)))
% 0.20/0.48         <= (~ (((sk_A) = (sk_C))) & 
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      ((((sk_A) = (sk_C))) | 
% 0.20/0.48       ~
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (~ (((sk_A) = (sk_C))) | 
% 0.20/0.48       ~
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_B @ sk_D_1))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X26 : $i]: ((k2_tarski @ X26 @ X26) = (k1_tarski @ X26))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.48         (((X1) != (X0))
% 0.20/0.48          | (r2_hidden @ X1 @ X2)
% 0.20/0.48          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.48  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['18', '20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_D_1)
% 0.20/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_D_1)) <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 0.20/0.48         ((r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X31))
% 0.20/0.48          | ~ (r2_hidden @ X29 @ X31)
% 0.20/0.48          | ~ (r2_hidden @ X27 @ X28))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((![X0 : $i, X1 : $i]:
% 0.20/0.48          (~ (r2_hidden @ X1 @ X0)
% 0.20/0.48           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D_1))))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((![X0 : $i]:
% 0.20/0.48          (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D_1)))
% 0.20/0.48         <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.48  thf('27', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D_1)))
% 0.20/0.48         <= (~
% 0.20/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) & 
% 0.20/0.48             (((sk_A) = (sk_C))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (~ (((sk_A) = (sk_C))) | 
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_B @ sk_D_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.20/0.48       ((r2_hidden @ sk_B @ sk_D_1))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.48         ((r2_hidden @ X29 @ X30)
% 0.20/0.48          | ~ (r2_hidden @ (k4_tarski @ X27 @ X29) @ (k2_zfmisc_1 @ X28 @ X30)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_D_1))
% 0.20/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_D_1)) <= (~ ((r2_hidden @ sk_B @ sk_D_1)))),
% 0.20/0.48      inference('split', [status(esa)], ['13'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (~
% 0.20/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.20/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.20/0.48       ((r2_hidden @ sk_B @ sk_D_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf('37', plain, ($false),
% 0.20/0.48      inference('sat_resolution*', [status(thm)],
% 0.20/0.48                ['1', '16', '17', '30', '31', '36'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
