%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ci4KDGowlH

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  79 expanded)
%              Number of leaves         :   13 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :  440 ( 824 expanded)
%              Number of equality atoms :   32 (  60 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ X35 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( sk_A = sk_C )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
    | ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A != sk_C )
      & ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( sk_A = sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_A != sk_C )
    | ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('18',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X38 ) )
      | ~ ( r2_hidden @ X36 @ X38 )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ X1 @ sk_B ) @ ( k2_zfmisc_1 @ X0 @ sk_D_1 ) ) )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ ( k4_tarski @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ sk_D_1 ) )
   <= ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
   <= ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('27',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_D_1 ) )
   <= ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
      & ( sk_A = sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A != sk_C )
    | ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['20'])).

thf('30',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ~ ( r2_hidden @ ( k4_tarski @ X34 @ X36 ) @ ( k2_zfmisc_1 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_D_1 )
   <= ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_D_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('34',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_C ) @ sk_D_1 ) )
    | ( r2_hidden @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','14','15','28','29','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ci4KDGowlH
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:30:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 59 iterations in 0.025s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(t128_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @
% 0.21/0.48         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48        ( ( r2_hidden @
% 0.21/0.48            ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ ( k1_tarski @ C ) @ D ) ) <=>
% 0.21/0.48          ( ( ( A ) = ( C ) ) & ( r2_hidden @ B @ D ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t128_zfmisc_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((((sk_A) = (sk_C))
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((((sk_A) = (sk_C))) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf(l54_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.48         ((r2_hidden @ X34 @ X35)
% 0.21/0.48          | ~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X37)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(t69_enumset1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('5', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf(d2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.21/0.48       ( ![D:$i]:
% 0.21/0.48         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.48          | ((X4) = (X3))
% 0.21/0.48          | ((X4) = (X0))
% 0.21/0.48          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (((X4) = (X0))
% 0.21/0.48          | ((X4) = (X3))
% 0.21/0.48          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((((sk_A) = (sk_C)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['4', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((~ (r2_hidden @ sk_B @ sk_D_1)
% 0.21/0.48        | ((sk_A) != (sk_C))
% 0.21/0.48        | ~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48             (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((sk_A) != (sk_A)))
% 0.21/0.48         <= (~ (((sk_A) = (sk_C))) & 
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['10', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_A) = (sk_C))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (~ (((sk_A) = (sk_C))) | 
% 0.21/0.48       ~
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_B @ sk_D_1))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('16', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (((X1) != (X0))
% 0.21/0.48          | (r2_hidden @ X1 @ X2)
% 0.21/0.48          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_tarski])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.48  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.21/0.48      inference('sup+', [status(thm)], ['16', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_D_1)
% 0.21/0.48        | (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((r2_hidden @ sk_B @ sk_D_1)) <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.21/0.48      inference('split', [status(esa)], ['20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X38))
% 0.21/0.48          | ~ (r2_hidden @ X36 @ X38)
% 0.21/0.48          | ~ (r2_hidden @ X34 @ X35))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((![X0 : $i, X1 : $i]:
% 0.21/0.48          (~ (r2_hidden @ X1 @ X0)
% 0.21/0.48           | (r2_hidden @ (k4_tarski @ X1 @ sk_B) @ (k2_zfmisc_1 @ X0 @ sk_D_1))))
% 0.21/0.48         <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((![X0 : $i]:
% 0.21/0.48          (r2_hidden @ (k4_tarski @ X0 @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ X0) @ sk_D_1)))
% 0.21/0.48         <= (((r2_hidden @ sk_B @ sk_D_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '23'])).
% 0.21/0.48  thf('25', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['11'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((~ (r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48           (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_D_1)))
% 0.21/0.48         <= (~
% 0.21/0.48             ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) & 
% 0.21/0.48             (((sk_A) = (sk_C))))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (~ (((sk_A) = (sk_C))) | 
% 0.21/0.48       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.21/0.48       ~ ((r2_hidden @ sk_B @ sk_D_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.21/0.48       ((r2_hidden @ sk_B @ sk_D_1))),
% 0.21/0.48      inference('split', [status(esa)], ['20'])).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1)))
% 0.21/0.48         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.48               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.48      inference('split', [status(esa)], ['0'])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.49         ((r2_hidden @ X36 @ X37)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X34 @ X36) @ (k2_zfmisc_1 @ X35 @ X37)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (((r2_hidden @ sk_B @ sk_D_1))
% 0.21/0.49         <= (((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49               (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_D_1)) <= (~ ((r2_hidden @ sk_B @ sk_D_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['11'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ 
% 0.21/0.49         (k2_zfmisc_1 @ (k1_tarski @ sk_C) @ sk_D_1))) | 
% 0.21/0.49       ((r2_hidden @ sk_B @ sk_D_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf('35', plain, ($false),
% 0.21/0.49      inference('sat_resolution*', [status(thm)],
% 0.21/0.49                ['1', '14', '15', '28', '29', '34'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
