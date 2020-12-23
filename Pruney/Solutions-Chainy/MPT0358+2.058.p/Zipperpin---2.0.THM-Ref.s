%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5HtW9ppSzH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:29 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 129 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  366 ( 974 expanded)
%              Number of equality atoms :   37 (  99 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('0',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('10',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X17: $i] :
      ( ( k1_subset_1 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('15',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('20',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('23',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['3','21','22'])).

thf('24',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X18 @ X19 )
        = ( k4_xboole_0 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('34',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( k1_subset_1 @ X17 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('37',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['3','21'])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5HtW9ppSzH
% 0.14/0.37  % Computer   : n016.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:40:34 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.23/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.48  % Solved by: fo/fo7.sh
% 0.23/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.48  % done 82 iterations in 0.032s
% 0.23/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.48  % SZS output start Refutation
% 0.23/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.48  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.23/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.23/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.23/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.48  thf(t38_subset_1, conjecture,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.23/0.48         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.23/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.48    (~( ![A:$i,B:$i]:
% 0.23/0.48        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.23/0.48            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.23/0.48    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.23/0.48  thf('0', plain,
% 0.23/0.48      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.23/0.48        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('1', plain,
% 0.23/0.48      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.23/0.48         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.23/0.48      inference('split', [status(esa)], ['0'])).
% 0.23/0.48  thf('2', plain,
% 0.23/0.48      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.23/0.48        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf('3', plain,
% 0.23/0.48      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.23/0.48       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.48      inference('split', [status(esa)], ['2'])).
% 0.23/0.48  thf(idempotence_k3_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.23/0.48  thf('4', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.23/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.23/0.48  thf(d7_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.23/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.23/0.48  thf('5', plain,
% 0.23/0.48      (![X4 : $i, X6 : $i]:
% 0.23/0.48         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 0.23/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.48  thf('6', plain,
% 0.23/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.23/0.48  thf('7', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.23/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.23/0.48  thf(d3_tarski, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.48  thf('8', plain,
% 0.23/0.48      (![X1 : $i, X3 : $i]:
% 0.23/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.48  thf('9', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.23/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.23/0.48  thf(t4_xboole_0, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.23/0.48  thf('10', plain,
% 0.23/0.48      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.23/0.48         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.23/0.48          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.23/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.23/0.48  thf('11', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i]:
% 0.23/0.48         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.48  thf('12', plain,
% 0.23/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['8', '11'])).
% 0.23/0.48  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.23/0.48      inference('sup-', [status(thm)], ['7', '12'])).
% 0.23/0.48  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.23/0.48  thf('14', plain, (![X17 : $i]: ((k1_subset_1 @ X17) = (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.48  thf('15', plain,
% 0.23/0.48      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('split', [status(esa)], ['0'])).
% 0.23/0.48  thf('16', plain,
% 0.23/0.48      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup+', [status(thm)], ['14', '15'])).
% 0.23/0.48  thf('17', plain,
% 0.23/0.48      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.23/0.48         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.23/0.48      inference('split', [status(esa)], ['2'])).
% 0.23/0.48  thf('18', plain,
% 0.23/0.48      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.23/0.48         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.23/0.48             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.48  thf('19', plain,
% 0.23/0.48      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('sup+', [status(thm)], ['14', '15'])).
% 0.23/0.48  thf('20', plain,
% 0.23/0.48      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.23/0.48         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.23/0.48             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.48  thf('21', plain,
% 0.23/0.48      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.23/0.48       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.48      inference('sup-', [status(thm)], ['13', '20'])).
% 0.23/0.48  thf('22', plain,
% 0.23/0.48      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.23/0.48       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.48      inference('split', [status(esa)], ['0'])).
% 0.23/0.48  thf('23', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.23/0.48      inference('sat_resolution*', [status(thm)], ['3', '21', '22'])).
% 0.23/0.48  thf('24', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.23/0.48      inference('simpl_trail', [status(thm)], ['1', '23'])).
% 0.23/0.48  thf('25', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.48  thf(d5_subset_1, axiom,
% 0.23/0.48    (![A:$i,B:$i]:
% 0.23/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.23/0.48  thf('26', plain,
% 0.23/0.48      (![X18 : $i, X19 : $i]:
% 0.23/0.48         (((k3_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))
% 0.23/0.48          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X18)))),
% 0.23/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.23/0.48  thf('27', plain,
% 0.23/0.48      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.23/0.48  thf(t106_xboole_1, axiom,
% 0.23/0.48    (![A:$i,B:$i,C:$i]:
% 0.23/0.48     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.23/0.48       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.23/0.48  thf('28', plain,
% 0.23/0.48      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.48         ((r1_xboole_0 @ X14 @ X16)
% 0.23/0.48          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 0.23/0.48      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.23/0.48  thf('29', plain,
% 0.23/0.48      (![X0 : $i]:
% 0.23/0.48         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.23/0.48          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.23/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.23/0.48  thf('30', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 0.23/0.48      inference('sup-', [status(thm)], ['24', '29'])).
% 0.23/0.48  thf('31', plain,
% 0.23/0.48      (![X4 : $i, X5 : $i]:
% 0.23/0.48         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 0.23/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.23/0.48  thf('32', plain, (((k3_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 0.23/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.48  thf('33', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 0.23/0.48      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.23/0.48  thf('34', plain, (((sk_B) = (k1_xboole_0))),
% 0.23/0.48      inference('demod', [status(thm)], ['32', '33'])).
% 0.23/0.48  thf('35', plain,
% 0.23/0.48      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.23/0.48         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('split', [status(esa)], ['2'])).
% 0.23/0.48  thf('36', plain, (![X17 : $i]: ((k1_subset_1 @ X17) = (k1_xboole_0))),
% 0.23/0.48      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.23/0.48  thf('37', plain,
% 0.23/0.48      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.23/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.23/0.48  thf('38', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.23/0.48      inference('sat_resolution*', [status(thm)], ['3', '21'])).
% 0.23/0.48  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.48      inference('simpl_trail', [status(thm)], ['37', '38'])).
% 0.23/0.48  thf('40', plain, ($false),
% 0.23/0.48      inference('simplify_reflect-', [status(thm)], ['34', '39'])).
% 0.23/0.48  
% 0.23/0.48  % SZS output end Refutation
% 0.23/0.48  
% 0.23/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
