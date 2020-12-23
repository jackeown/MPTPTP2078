%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PpFdJNxUCy

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:41 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 112 expanded)
%              Number of leaves         :   14 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :  243 ( 933 expanded)
%              Number of equality atoms :   14 (  54 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

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
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X0 ) @ ( sk_E @ X0 ) )
        = X0 )
      | ~ ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('5',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('8',plain,
    ( ( k1_mcart_1 @ sk_A )
    = ( sk_D @ sk_A ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('10',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf('11',plain,(
    ! [X8: $i,X10: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X8 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('12',plain,
    ( ( k2_mcart_1 @ sk_A )
    = ( sk_E @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k4_tarski @ ( k1_mcart_1 @ sk_A ) @ ( k2_mcart_1 @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ sk_A @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['21','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PpFdJNxUCy
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 32 iterations in 0.017s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.44  thf(sk_E_type, type, sk_E: $i > $i).
% 0.19/0.44  thf(sk_D_type, type, sk_D: $i > $i).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.44  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.44  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.44  thf(t10_mcart_1, conjecture,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.44       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.44         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.44        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.19/0.44          ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.19/0.44            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t10_mcart_1])).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.19/0.44        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('1', plain,
% 0.19/0.44      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))
% 0.19/0.44         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)))),
% 0.19/0.44      inference('split', [status(esa)], ['0'])).
% 0.19/0.44  thf('2', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('3', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(l139_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i]:
% 0.19/0.44     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.19/0.44          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.19/0.44  thf('4', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.44         (((k4_tarski @ (sk_D @ X0) @ (sk_E @ X0)) = (X0))
% 0.19/0.44          | ~ (r2_hidden @ X0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.19/0.44      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.19/0.44  thf('5', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.44  thf('6', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.44  thf(t7_mcart_1, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.44       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      (![X8 : $i, X9 : $i]: ((k1_mcart_1 @ (k4_tarski @ X8 @ X9)) = (X8))),
% 0.19/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.44  thf('8', plain, (((k1_mcart_1 @ sk_A) = (sk_D @ sk_A))),
% 0.19/0.44      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.44  thf('9', plain,
% 0.19/0.44      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['5', '8'])).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['5', '8'])).
% 0.19/0.44  thf('11', plain,
% 0.19/0.44      (![X8 : $i, X10 : $i]: ((k2_mcart_1 @ (k4_tarski @ X8 @ X10)) = (X10))),
% 0.19/0.44      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.44  thf('12', plain, (((k2_mcart_1 @ sk_A) = (sk_E @ sk_A))),
% 0.19/0.44      inference('sup+', [status(thm)], ['10', '11'])).
% 0.19/0.44  thf('13', plain,
% 0.19/0.44      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['9', '12'])).
% 0.19/0.44  thf(l54_zfmisc_1, axiom,
% 0.19/0.44    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.44     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.19/0.44       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.44         ((r2_hidden @ X3 @ X4)
% 0.19/0.44          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.19/0.44      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.19/0.44          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ X1))),
% 0.19/0.44      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.44  thf('16', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.19/0.44      inference('sup-', [status(thm)], ['2', '15'])).
% 0.19/0.44  thf('17', plain,
% 0.19/0.44      ((~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))
% 0.19/0.44         <= (~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)))),
% 0.19/0.44      inference('split', [status(esa)], ['0'])).
% 0.19/0.44  thf('18', plain, (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.19/0.44      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.44  thf('19', plain,
% 0.19/0.44      (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)) | 
% 0.19/0.44       ~ ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B))),
% 0.19/0.44      inference('split', [status(esa)], ['0'])).
% 0.19/0.44  thf('20', plain, (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C))),
% 0.19/0.44      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.19/0.44  thf('21', plain, (~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 0.19/0.44      inference('simpl_trail', [status(thm)], ['1', '20'])).
% 0.19/0.44  thf('22', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('23', plain,
% 0.19/0.44      (((k4_tarski @ (k1_mcart_1 @ sk_A) @ (k2_mcart_1 @ sk_A)) = (sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['9', '12'])).
% 0.19/0.44  thf('24', plain,
% 0.19/0.44      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.44         ((r2_hidden @ X5 @ X6)
% 0.19/0.44          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 0.19/0.44      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.19/0.44  thf('25', plain,
% 0.19/0.44      (![X0 : $i, X1 : $i]:
% 0.19/0.44         (~ (r2_hidden @ sk_A @ (k2_zfmisc_1 @ X1 @ X0))
% 0.19/0.44          | (r2_hidden @ (k2_mcart_1 @ sk_A) @ X0))),
% 0.19/0.44      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.44  thf('26', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C)),
% 0.19/0.44      inference('sup-', [status(thm)], ['22', '25'])).
% 0.19/0.44  thf('27', plain, ($false), inference('demod', [status(thm)], ['21', '26'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
