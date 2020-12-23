%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1G99hsAdP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 167 expanded)
%              Number of leaves         :   19 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :  383 (1360 expanded)
%              Number of equality atoms :   38 ( 139 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('2',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('17',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['7'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('25',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['8','23','24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['6','25'])).

thf('27',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('28',plain,(
    ! [X14: $i] :
      ( ( k1_subset_1 @ X14 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('29',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','23'])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['26','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X15 @ X16 )
        = ( k4_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','38'])).

thf('40',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n1G99hsAdP
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 77 iterations in 0.040s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(t7_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.50  thf('0', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X10 : $i]:
% 0.20/0.50         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.50  thf(t38_subset_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.50         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.50            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.20/0.50        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.50         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.50          | (r2_hidden @ X0 @ X2)
% 0.20/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.50           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.20/0.50         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (((((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))))
% 0.20/0.50         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.20/0.50        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.20/0.50       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf(t3_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.50  thf('10', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.20/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.50  thf(d5_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ X7)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ X6)
% 0.20/0.50          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.20/0.50  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('condensation', [status(thm)], ['13'])).
% 0.20/0.50  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.50  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('16', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.20/0.50         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.50             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.20/0.50         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.20/0.50             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.50       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.20/0.50       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.50      inference('split', [status(esa)], ['2'])).
% 0.20/0.50  thf('25', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['8', '23', '24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['6', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.20/0.50         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('split', [status(esa)], ['7'])).
% 0.20/0.50  thf('28', plain, (![X14 : $i]: ((k1_subset_1 @ X14) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.50  thf('30', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['8', '23'])).
% 0.20/0.50  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['26', '31'])).
% 0.20/0.50  thf('33', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d5_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i]:
% 0.20/0.50         (((k3_subset_1 @ X15 @ X16) = (k4_xboole_0 @ X15 @ X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X8 @ X6)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.20/0.50          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.20/0.50      inference('sup-', [status(thm)], ['32', '37'])).
% 0.20/0.50  thf('39', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '38'])).
% 0.20/0.50  thf('40', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.20/0.50  thf('41', plain, ($false),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
