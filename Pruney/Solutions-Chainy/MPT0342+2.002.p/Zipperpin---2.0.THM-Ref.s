%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFRef6VU51

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:35 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   52 (  68 expanded)
%              Number of leaves         :   14 (  26 expanded)
%              Depth                    :   15
%              Number of atoms          :  320 ( 515 expanded)
%              Number of equality atoms :    3 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t7_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                   => ( r2_hidden @ D @ C ) ) )
             => ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['10','18'])).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('21',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X15: $i] :
      ( ~ ( r2_hidden @ X15 @ sk_B_1 )
      | ( r2_hidden @ X15 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X15 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFRef6VU51
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:34:54 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 136 iterations in 0.065s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.55  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.23/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.55  thf(t7_subset_1, conjecture,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55       ( ![C:$i]:
% 0.23/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55           ( ( ![D:$i]:
% 0.23/0.55               ( ( m1_subset_1 @ D @ A ) =>
% 0.23/0.55                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.23/0.55             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i,B:$i]:
% 0.23/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55          ( ![C:$i]:
% 0.23/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.55              ( ( ![D:$i]:
% 0.23/0.55                  ( ( m1_subset_1 @ D @ A ) =>
% 0.23/0.55                    ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.23/0.55                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t7_subset_1])).
% 0.23/0.55  thf('0', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(d3_tarski, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.55  thf('1', plain,
% 0.23/0.55      (![X4 : $i, X6 : $i]:
% 0.23/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(d2_subset_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.23/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.23/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.23/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.55  thf('3', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         (~ (m1_subset_1 @ X12 @ X13)
% 0.23/0.55          | (r2_hidden @ X12 @ X13)
% 0.23/0.55          | (v1_xboole_0 @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.55        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.55  thf(d1_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.23/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X10 @ X9)
% 0.23/0.55          | (r1_tarski @ X10 @ X8)
% 0.23/0.55          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X8 : $i, X10 : $i]:
% 0.23/0.55         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.23/0.55  thf('7', plain,
% 0.23/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.23/0.55         (~ (r1_tarski @ X7 @ X8)
% 0.23/0.55          | (r2_hidden @ X7 @ X9)
% 0.23/0.55          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         ((r2_hidden @ X7 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X7 @ X8))),
% 0.23/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.23/0.55  thf('10', plain,
% 0.23/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.23/0.55        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.23/0.55  thf('11', plain,
% 0.23/0.55      (![X4 : $i, X6 : $i]:
% 0.23/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('12', plain,
% 0.23/0.55      (![X4 : $i, X6 : $i]:
% 0.23/0.55         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('13', plain,
% 0.23/0.55      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.55  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.23/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         ((r2_hidden @ X7 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X7 @ X8))),
% 0.23/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.23/0.55  thf('16', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.23/0.55  thf(d1_xboole_0, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.23/0.55  thf('17', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.55  thf('18', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.23/0.55  thf('19', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.55      inference('clc', [status(thm)], ['10', '18'])).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (![X8 : $i, X10 : $i]:
% 0.23/0.55         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.23/0.55  thf('21', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 0.23/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.23/0.55  thf('22', plain,
% 0.23/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X3 @ X4)
% 0.23/0.55          | (r2_hidden @ X3 @ X5)
% 0.23/0.55          | ~ (r1_tarski @ X4 @ X5))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('23', plain,
% 0.23/0.55      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.55  thf('24', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['1', '23'])).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X12 @ X13)
% 0.23/0.55          | (m1_subset_1 @ X12 @ X13)
% 0.23/0.55          | (v1_xboole_0 @ X13))),
% 0.23/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.23/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i]:
% 0.23/0.55         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 0.23/0.55      inference('clc', [status(thm)], ['25', '26'])).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_B_1 @ X0)
% 0.23/0.55          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['24', '27'])).
% 0.23/0.55  thf('29', plain,
% 0.23/0.55      (![X15 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X15 @ sk_B_1)
% 0.23/0.55          | (r2_hidden @ X15 @ sk_C_2)
% 0.23/0.55          | ~ (m1_subset_1 @ X15 @ sk_A))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('30', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r1_tarski @ sk_B_1 @ X0)
% 0.23/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)
% 0.23/0.55          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      (![X4 : $i, X6 : $i]:
% 0.23/0.55         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)
% 0.23/0.55          | (r1_tarski @ sk_B_1 @ X0))),
% 0.23/0.55      inference('clc', [status(thm)], ['30', '31'])).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      (![X4 : $i, X6 : $i]:
% 0.23/0.55         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.55  thf('34', plain,
% 0.23/0.55      (((r1_tarski @ sk_B_1 @ sk_C_2) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 0.23/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.23/0.55  thf('35', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.23/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.23/0.55  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
