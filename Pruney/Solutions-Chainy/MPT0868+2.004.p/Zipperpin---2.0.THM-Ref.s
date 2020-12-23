%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GtlS9YkakM

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 101 expanded)
%              Number of leaves         :   22 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  429 ( 925 expanded)
%              Number of equality atoms :   70 ( 159 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t26_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( ( C
                   != ( k1_mcart_1 @ C ) )
                  & ( C
                   != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_mcart_1])).

thf('0',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k4_tarski @ ( k1_mcart_1 @ X13 ) @ ( k2_mcart_1 @ X13 ) ) )
      | ~ ( v1_relat_1 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( sk_C
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k2_mcart_1 @ X10 ) )
      | ( X10
       != ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_tarski @ X11 @ X12 )
     != ( k2_mcart_1 @ ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X15 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_tarski @ X11 @ X12 )
     != X12 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('17',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X10
       != ( k1_mcart_1 @ X10 ) )
      | ( X10
       != ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_tarski @ X11 @ X12 )
     != ( k1_mcart_1 @ ( k4_tarski @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_tarski @ X11 @ X12 )
     != X11 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','21'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('23',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('26',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GtlS9YkakM
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:11:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 60 iterations in 0.036s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(t26_mcart_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ~( ![C:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.19/0.48                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.19/0.48                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48             ( ~( ![C:$i]:
% 0.19/0.48                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.19/0.48                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.19/0.48                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('2', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t2_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]:
% 0.19/0.48         ((r2_hidden @ X6 @ X7)
% 0.19/0.48          | (v1_xboole_0 @ X7)
% 0.19/0.48          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.19/0.48        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf(t23_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r2_hidden @ A @ B ) =>
% 0.19/0.48         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]:
% 0.19/0.48         (((X13) = (k4_tarski @ (k1_mcart_1 @ X13) @ (k2_mcart_1 @ X13)))
% 0.19/0.48          | ~ (v1_relat_1 @ X14)
% 0.19/0.48          | ~ (r2_hidden @ X13 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.19/0.48        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.19/0.48        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.48  thf(fc6_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.19/0.48        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.19/0.48         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.19/0.48         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['1', '8'])).
% 0.19/0.48  thf(t20_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.48       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (((X10) != (k2_mcart_1 @ X10)) | ((X10) != (k4_tarski @ X11 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k4_tarski @ X11 @ X12) != (k2_mcart_1 @ (k4_tarski @ X11 @ X12)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.48  thf(t7_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (![X15 : $i, X17 : $i]: ((k2_mcart_1 @ (k4_tarski @ X15 @ X17)) = (X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('13', plain, (![X11 : $i, X12 : $i]: ((k4_tarski @ X11 @ X12) != (X12))),
% 0.19/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.19/0.48         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['9', '13'])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.19/0.48        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['6', '7'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.19/0.48         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))))
% 0.19/0.48         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.48         (((X10) != (k1_mcart_1 @ X10)) | ((X10) != (k4_tarski @ X11 @ X12)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         ((k4_tarski @ X11 @ X12) != (k1_mcart_1 @ (k4_tarski @ X11 @ X12)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]: ((k1_mcart_1 @ (k4_tarski @ X15 @ X16)) = (X15))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('21', plain, (![X11 : $i, X12 : $i]: ((k4_tarski @ X11 @ X12) != (X11))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.19/0.48         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['17', '21'])).
% 0.19/0.48  thf(t9_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.48                 ( ![C:$i,D:$i]:
% 0.19/0.48                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.48                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (![X18 : $i]:
% 0.19/0.48         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X18) @ X18))),
% 0.19/0.48      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.48  thf(d1_xboole_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.19/0.48  thf(t113_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (![X3 : $i, X4 : $i]:
% 0.19/0.48         (((X3) = (k1_xboole_0))
% 0.19/0.48          | ((X4) = (k1_xboole_0))
% 0.19/0.48          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.48         (((k2_zfmisc_1 @ X2 @ X1) != (X0))
% 0.19/0.48          | ~ (v1_xboole_0 @ X0)
% 0.19/0.48          | ((X2) = (k1_xboole_0))
% 0.19/0.48          | ((X1) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         (((X1) = (k1_xboole_0))
% 0.19/0.48          | ((X2) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (((((sk_A) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0))))
% 0.19/0.48         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['22', '28'])).
% 0.19/0.48  thf('30', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('32', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['29', '30', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['0'])).
% 0.19/0.48  thf('34', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.19/0.48  thf('35', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['14', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i]:
% 0.19/0.48         (((X1) = (k1_xboole_0))
% 0.19/0.48          | ((X2) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.48  thf('37', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.48  thf('38', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('40', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
