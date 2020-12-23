%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ieQazEiFM9

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:22 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 139 expanded)
%              Number of leaves         :   18 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  411 (1147 expanded)
%              Number of equality atoms :   37 (  97 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ ( k4_xboole_0 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('4',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r2_hidden @ X10 @ X7 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X15: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X15 @ X17 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(demod,[status(thm)],['18','24'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('27',plain,
    ( ( sk_B
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['7'])).

thf('30',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('32',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
      & ( sk_B
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('35',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['8','33','34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['6','35'])).

thf('37',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','36'])).

thf('38',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('39',plain,
    ( ( sk_B
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('40',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_B
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['8','33'])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ieQazEiFM9
% 0.12/0.35  % Computer   : n005.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 18:08:03 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.47/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.67  % Solved by: fo/fo7.sh
% 0.47/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.67  % done 343 iterations in 0.214s
% 0.47/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.67  % SZS output start Refutation
% 0.47/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.47/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.47/0.67  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.47/0.67  thf(t38_subset_1, conjecture,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.47/0.67         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.47/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.67    (~( ![A:$i,B:$i]:
% 0.47/0.67        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.47/0.67            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.47/0.67    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.47/0.67  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf(d5_subset_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.47/0.67       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.47/0.67  thf('1', plain,
% 0.47/0.67      (![X33 : $i, X34 : $i]:
% 0.47/0.67         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.47/0.67          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.47/0.67  thf('2', plain,
% 0.47/0.67      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.67  thf(t38_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.47/0.67       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.67  thf('3', plain,
% 0.47/0.67      (![X22 : $i, X23 : $i]:
% 0.47/0.67         (((X22) = (k1_xboole_0))
% 0.47/0.67          | ~ (r1_tarski @ X22 @ (k4_xboole_0 @ X23 @ X22)))),
% 0.47/0.67      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.47/0.67  thf('4', plain,
% 0.47/0.67      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.47/0.67        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.67  thf('5', plain,
% 0.47/0.67      ((((sk_B) = (k1_subset_1 @ sk_A))
% 0.47/0.67        | (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('6', plain,
% 0.47/0.67      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.47/0.67         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.47/0.67      inference('split', [status(esa)], ['5'])).
% 0.47/0.67  thf('7', plain,
% 0.47/0.67      ((((sk_B) != (k1_subset_1 @ sk_A))
% 0.47/0.67        | ~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.67  thf('8', plain,
% 0.47/0.67      (~ (((sk_B) = (k1_subset_1 @ sk_A))) | 
% 0.47/0.67       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('split', [status(esa)], ['7'])).
% 0.47/0.67  thf(d3_tarski, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( r1_tarski @ A @ B ) <=>
% 0.47/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.47/0.67  thf('9', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i]:
% 0.47/0.67         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf(d5_xboole_0, axiom,
% 0.47/0.67    (![A:$i,B:$i,C:$i]:
% 0.47/0.67     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.47/0.67       ( ![D:$i]:
% 0.47/0.67         ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.67           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.47/0.67  thf('10', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X10 @ X9)
% 0.47/0.67          | (r2_hidden @ X10 @ X7)
% 0.47/0.67          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.67  thf('11', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.47/0.67         ((r2_hidden @ X10 @ X7)
% 0.47/0.67          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['10'])).
% 0.47/0.67  thf('12', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.47/0.67          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['9', '11'])).
% 0.47/0.67  thf('13', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i]:
% 0.47/0.67         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('14', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X10 @ X9)
% 0.47/0.67          | ~ (r2_hidden @ X10 @ X8)
% 0.47/0.67          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 0.47/0.67      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.47/0.67  thf('15', plain,
% 0.47/0.67      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.47/0.67         (~ (r2_hidden @ X10 @ X8)
% 0.47/0.67          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.47/0.67      inference('simplify', [status(thm)], ['14'])).
% 0.47/0.67  thf('16', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.67         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.47/0.67          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['13', '15'])).
% 0.47/0.67  thf('17', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]:
% 0.47/0.67         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.47/0.67          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.47/0.67      inference('sup-', [status(thm)], ['12', '16'])).
% 0.47/0.67  thf('18', plain,
% 0.47/0.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.47/0.67      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.67  thf('19', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i]:
% 0.47/0.67         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('20', plain,
% 0.47/0.67      (![X3 : $i, X5 : $i]:
% 0.47/0.67         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_tarski])).
% 0.47/0.67  thf('21', plain,
% 0.47/0.67      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['19', '20'])).
% 0.47/0.67  thf('22', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.47/0.67      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.67  thf(l32_xboole_1, axiom,
% 0.47/0.67    (![A:$i,B:$i]:
% 0.47/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.67  thf('23', plain,
% 0.47/0.67      (![X15 : $i, X17 : $i]:
% 0.47/0.67         (((k4_xboole_0 @ X15 @ X17) = (k1_xboole_0))
% 0.47/0.67          | ~ (r1_tarski @ X15 @ X17))),
% 0.47/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.67  thf('24', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.67      inference('sup-', [status(thm)], ['22', '23'])).
% 0.47/0.67  thf('25', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.47/0.67      inference('demod', [status(thm)], ['18', '24'])).
% 0.47/0.67  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.47/0.67  thf('26', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.47/0.67  thf('27', plain,
% 0.47/0.67      ((((sk_B) = (k1_subset_1 @ sk_A))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('split', [status(esa)], ['5'])).
% 0.47/0.67  thf('28', plain,
% 0.47/0.67      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.47/0.67  thf('29', plain,
% 0.47/0.67      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))
% 0.47/0.67         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))))),
% 0.47/0.67      inference('split', [status(esa)], ['7'])).
% 0.47/0.67  thf('30', plain,
% 0.47/0.67      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.47/0.67         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.47/0.67             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['28', '29'])).
% 0.47/0.67  thf('31', plain,
% 0.47/0.67      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('sup+', [status(thm)], ['26', '27'])).
% 0.47/0.67  thf('32', plain,
% 0.47/0.67      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.47/0.67         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) & 
% 0.47/0.67             (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('demod', [status(thm)], ['30', '31'])).
% 0.47/0.67  thf('33', plain,
% 0.47/0.67      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.47/0.67       ~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.47/0.67      inference('sup-', [status(thm)], ['25', '32'])).
% 0.47/0.67  thf('34', plain,
% 0.47/0.67      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.47/0.67       (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.47/0.67      inference('split', [status(esa)], ['5'])).
% 0.47/0.67  thf('35', plain, (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['8', '33', '34'])).
% 0.47/0.67  thf('36', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['6', '35'])).
% 0.47/0.67  thf('37', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.67      inference('demod', [status(thm)], ['4', '36'])).
% 0.47/0.67  thf('38', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.47/0.67      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.47/0.67  thf('39', plain,
% 0.47/0.67      ((((sk_B) != (k1_subset_1 @ sk_A)))
% 0.47/0.67         <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('split', [status(esa)], ['7'])).
% 0.47/0.67  thf('40', plain,
% 0.47/0.67      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_subset_1 @ sk_A))))),
% 0.47/0.67      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.67  thf('41', plain, (~ (((sk_B) = (k1_subset_1 @ sk_A)))),
% 0.47/0.67      inference('sat_resolution*', [status(thm)], ['8', '33'])).
% 0.47/0.67  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.47/0.67      inference('simpl_trail', [status(thm)], ['40', '41'])).
% 0.47/0.67  thf('43', plain, ($false),
% 0.47/0.67      inference('simplify_reflect-', [status(thm)], ['37', '42'])).
% 0.47/0.67  
% 0.47/0.67  % SZS output end Refutation
% 0.47/0.67  
% 0.47/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
