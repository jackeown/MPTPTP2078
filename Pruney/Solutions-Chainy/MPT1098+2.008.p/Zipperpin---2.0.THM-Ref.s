%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FcM8JKeJ0U

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   50 (  72 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  386 ( 751 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('1',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_finset_1 @ X7 )
      | ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ ( sk_D @ X8 @ X9 @ X7 ) @ ( sk_E @ X8 @ X9 @ X7 ) ) )
      | ~ ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_finset_1 @ X7 )
      | ( r1_tarski @ ( sk_E @ X8 @ X9 @ X7 ) @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('11',plain,
    ( ( r1_tarski @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X4 ) @ ( k2_zfmisc_1 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_zfmisc_1 @ X0 @ ( sk_E @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) )
    | ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X10: $i] :
      ( ~ ( v1_finset_1 @ X10 )
      | ~ ( r1_tarski @ X10 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X10 @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_finset_1 @ X7 )
      | ( r1_tarski @ ( sk_D @ X8 @ X9 @ X7 ) @ X9 )
      | ~ ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('26',plain,
    ( ( r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    r1_tarski @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_finset_1 @ X7 )
      | ( v1_finset_1 @ ( sk_D @ X8 @ X9 @ X7 ) )
      | ~ ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('31',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_finset_1 @ ( sk_D @ sk_C_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['23','28','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FcM8JKeJ0U
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:59:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 107 iterations in 0.064s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.21/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(d3_tarski, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.53  thf('0', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf(t33_finset_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.53          ( ![D:$i]:
% 0.21/0.53            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.21/0.53                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.53        ( ~( ( v1_finset_1 @ A ) & 
% 0.21/0.53             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.53             ( ![D:$i]:
% 0.21/0.53               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.21/0.53                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 0.21/0.53  thf('1', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t32_finset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.53          ( ![D:$i,E:$i]:
% 0.21/0.53            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.21/0.53                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 0.21/0.53                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v1_finset_1 @ X7)
% 0.21/0.53          | (r1_tarski @ X7 @ 
% 0.21/0.53             (k2_zfmisc_1 @ (sk_D @ X8 @ X9 @ X7) @ (sk_E @ X8 @ X9 @ X7)))
% 0.21/0.53          | ~ (r1_tarski @ X7 @ (k2_zfmisc_1 @ X9 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (((r1_tarski @ sk_A @ 
% 0.21/0.53         (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.21/0.53          (sk_E @ sk_C_1 @ sk_B @ sk_A)))
% 0.21/0.53        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      ((r1_tarski @ sk_A @ 
% 0.21/0.53        (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.21/0.53         (sk_E @ sk_C_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r2_hidden @ X0 @ 
% 0.21/0.53           (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.21/0.53            (sk_E @ sk_C_1 @ sk_B @ sk_A)))
% 0.21/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_A @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.21/0.53             (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.21/0.53              (sk_E @ sk_C_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '7'])).
% 0.21/0.53  thf('9', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v1_finset_1 @ X7)
% 0.21/0.53          | (r1_tarski @ (sk_E @ X8 @ X9 @ X7) @ X8)
% 0.21/0.53          | ~ (r1_tarski @ X7 @ (k2_zfmisc_1 @ X9 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      (((r1_tarski @ (sk_E @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)
% 0.21/0.53        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.53  thf('12', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('13', plain, ((r1_tarski @ (sk_E @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)),
% 0.21/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(t118_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.21/0.53         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.53          | (r1_tarski @ (k2_zfmisc_1 @ X6 @ X4) @ (k2_zfmisc_1 @ X6 @ X5)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.21/0.53  thf('15', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.21/0.53          (k2_zfmisc_1 @ X0 @ sk_C_1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.53          | (r2_hidden @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         ((r2_hidden @ X1 @ (k2_zfmisc_1 @ X0 @ sk_C_1))
% 0.21/0.53          | ~ (r2_hidden @ X1 @ 
% 0.21/0.53               (k2_zfmisc_1 @ X0 @ (sk_E @ sk_C_1 @ sk_B @ sk_A))))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ sk_A @ X0)
% 0.21/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ 
% 0.21/0.53             (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X1 : $i, X3 : $i]:
% 0.21/0.53         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((r1_tarski @ sk_A @ 
% 0.21/0.53         (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1))
% 0.21/0.53        | (r1_tarski @ sk_A @ 
% 0.21/0.53           (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      ((r1_tarski @ sk_A @ 
% 0.21/0.53        (k2_zfmisc_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_C_1))),
% 0.21/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X10 : $i]:
% 0.21/0.53         (~ (v1_finset_1 @ X10)
% 0.21/0.53          | ~ (r1_tarski @ X10 @ sk_B)
% 0.21/0.53          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X10 @ sk_C_1)))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      ((~ (r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.53        | ~ (v1_finset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.53  thf('24', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v1_finset_1 @ X7)
% 0.21/0.53          | (r1_tarski @ (sk_D @ X8 @ X9 @ X7) @ X9)
% 0.21/0.53          | ~ (r1_tarski @ X7 @ (k2_zfmisc_1 @ X9 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)
% 0.21/0.53        | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('28', plain, ((r1_tarski @ (sk_D @ sk_C_1 @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.53  thf('29', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.53         (~ (v1_finset_1 @ X7)
% 0.21/0.53          | (v1_finset_1 @ (sk_D @ X8 @ X9 @ X7))
% 0.21/0.53          | ~ (r1_tarski @ X7 @ (k2_zfmisc_1 @ X9 @ X8)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (((v1_finset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain, ((v1_finset_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('33', plain, ((v1_finset_1 @ (sk_D @ sk_C_1 @ sk_B @ sk_A))),
% 0.21/0.53      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.53  thf('34', plain, ($false),
% 0.21/0.53      inference('demod', [status(thm)], ['23', '28', '33'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
