%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bnvCydbH60

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:28 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 147 expanded)
%              Number of leaves         :   23 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  430 (1140 expanded)
%              Number of equality atoms :   40 ( 104 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('8',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('24',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('25',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('27',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('29',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('32',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['6','30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['4','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('36',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['33','38'])).

thf('40',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','39'])).

thf('41',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('42',plain,(
    ! [X21: $i] :
      ( ( k1_subset_1 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('43',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','30'])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bnvCydbH60
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:46:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.19/0.33  % Python version: Python 3.6.8
% 0.19/0.33  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 133 iterations in 0.050s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(t7_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (![X10 : $i]:
% 0.19/0.49         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.49  thf(t38_subset_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.49         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.19/0.49            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.19/0.49        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.19/0.49         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf(d3_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.49          | (r2_hidden @ X0 @ X2)
% 0.19/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.19/0.49           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 0.19/0.49         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.19/0.49        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.19/0.49       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('split', [status(esa)], ['5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf(t5_boole, axiom,
% 0.19/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.49  thf('8', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t5_boole])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X1 : $i, X3 : $i]:
% 0.19/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('12', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.49  thf(t28_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i]:
% 0.19/0.49         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.19/0.49      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.49  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.49  thf(t100_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i]:
% 0.19/0.49         ((k4_xboole_0 @ X11 @ X12)
% 0.19/0.49           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf(d5_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.19/0.49          | ~ (r2_hidden @ X8 @ X6)
% 0.19/0.49          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.49          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.19/0.49          | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['16', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '19'])).
% 0.19/0.49  thf('21', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.49  thf('22', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '21'])).
% 0.19/0.49  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('23', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.19/0.49         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.19/0.49      inference('split', [status(esa)], ['5'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.19/0.49             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.49         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.19/0.49             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.19/0.49       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.19/0.49       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf('32', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['6', '30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.19/0.49          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['4', '32'])).
% 0.19/0.49  thf('34', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d5_subset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.49       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X22 : $i, X23 : $i]:
% 0.19/0.49         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X8 @ X6)
% 0.19/0.49          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.19/0.49          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.49  thf('39', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1)),
% 0.19/0.49      inference('clc', [status(thm)], ['33', '38'])).
% 0.19/0.49  thf('40', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.19/0.49         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('split', [status(esa)], ['5'])).
% 0.19/0.49  thf('42', plain, (![X21 : $i]: ((k1_subset_1 @ X21) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['6', '30'])).
% 0.19/0.49  thf('45', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['43', '44'])).
% 0.19/0.49  thf('46', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['40', '45'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
