%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tduCs9woYu

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 154 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  419 (1113 expanded)
%              Number of equality atoms :   68 ( 158 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t66_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
         != k1_xboole_0 )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
           => ( ( C
               != ( k1_mcart_1 @ C ) )
              & ( C
               != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_mcart_1])).

thf('4',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(fc3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ B )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X8 @ X9 ) )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc3_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['6','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13
       != ( k1_mcart_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k2_zfmisc_1 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('17',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k1_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13
       != ( k2_mcart_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k2_zfmisc_1 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('23',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k2_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( ( r1_xboole_0 @ X3 @ X3 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('32',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','36'])).

thf('42',plain,(
    sk_C
 != ( k2_mcart_1 @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['18'])).

thf('44',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['19','44'])).

thf('46',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C != sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['28'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','36'])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','36'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['14','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tduCs9woYu
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:45:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 59 iterations in 0.035s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(fc4_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X10) | (v1_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.21/0.49  thf(t6_boole, axiom,
% 0.21/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_boole])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_boole])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf(t66_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49       ( ![C:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.49           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i]:
% 0.21/0.49        ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.49          ( ![C:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.49              ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.21/0.49                ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t66_mcart_1])).
% 0.21/0.49  thf('4', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((X0) != (k1_xboole_0))
% 0.21/0.49          | ~ (v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.49        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.49  thf(fc3_zfmisc_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_xboole_0 @ B ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 0.21/0.49      inference('cnf', [status(esa)], [t6_boole])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ (k2_zfmisc_1 @ X8 @ X9)) | ~ (v1_xboole_0 @ X9))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc3_zfmisc_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v1_xboole_0 @ k1_xboole_0)
% 0.21/0.49          | ~ (v1_xboole_0 @ X0)
% 0.21/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.49  thf('13', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('clc', [status(thm)], ['6', '12'])).
% 0.21/0.49  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '13'])).
% 0.21/0.49  thf('15', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t26_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ~( ![C:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.49                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.21/0.49                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (((X12) = (k1_xboole_0))
% 0.21/0.49          | ((X13) != (k1_mcart_1 @ X13))
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (k2_zfmisc_1 @ X12 @ X14))
% 0.21/0.49          | ((X14) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_C) != (k1_mcart_1 @ sk_C))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('21', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.49         (((X12) = (k1_xboole_0))
% 0.21/0.49          | ((X13) != (k2_mcart_1 @ X13))
% 0.21/0.49          | ~ (m1_subset_1 @ X13 @ (k2_zfmisc_1 @ X12 @ X14))
% 0.21/0.49          | ((X14) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_C) != (k2_mcart_1 @ sk_C))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (((((sk_C) != (sk_C))
% 0.21/0.49         | ((sk_A) = (k1_xboole_0))
% 0.21/0.49         | ((sk_B) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_xboole_0 @ X0) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.49  thf('27', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '29'])).
% 0.21/0.49  thf(t66_xboole_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.21/0.49       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X3 : $i]: ((r1_xboole_0 @ X3 @ X3) | ((X3) != (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.21/0.49  thf('32', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.49  thf(t69_xboole_1, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.49       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X5 : $i, X6 : $i]:
% 0.21/0.49         (~ (r1_xboole_0 @ X5 @ X6)
% 0.21/0.49          | ~ (r1_tarski @ X5 @ X6)
% 0.21/0.49          | (v1_xboole_0 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('36', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.49      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.49  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('demod', [status(thm)], ['30', '37'])).
% 0.21/0.49  thf('39', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '13'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '36'])).
% 0.21/0.49  thf('42', plain, (~ (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) | (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('44', plain, ((((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain, (((sk_C) = (k1_mcart_1 @ sk_C))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['19', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_C) != (sk_C))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['17', '45'])).
% 0.21/0.49  thf('47', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.49  thf('48', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.21/0.49      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.49  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '36'])).
% 0.21/0.49  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.49  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '36'])).
% 0.21/0.49  thf('53', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '51', '52'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
