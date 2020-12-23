%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ITbsEHqcaL

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 146 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   18
%              Number of atoms          :  514 (1317 expanded)
%              Number of equality atoms :   85 ( 221 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k4_tarski @ ( k1_mcart_1 @ X11 ) @ ( k2_mcart_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( sk_C
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8
       != ( k2_mcart_1 @ X8 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != ( k2_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('12',plain,(
    ! [X13: $i,X15: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != X10 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
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
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('17',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8
       != ( k1_mcart_1 @ X8 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('19',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != ( k1_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != X9 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','21'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','21'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('36',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = sk_B )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k1_xboole_0 = sk_B )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['14','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X7 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_xboole_0 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ITbsEHqcaL
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 60 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(t26_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ~( ![C:$i]:
% 0.20/0.49               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.49                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.49                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49             ( ~( ![C:$i]:
% 0.20/0.49                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.49                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.49                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('2', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t2_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X1 : $i, X2 : $i]:
% 0.20/0.49         ((r2_hidden @ X1 @ X2)
% 0.20/0.49          | (v1_xboole_0 @ X2)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.49        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(t23_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.49         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X11 : $i, X12 : $i]:
% 0.20/0.49         (((X11) = (k4_tarski @ (k1_mcart_1 @ X11) @ (k2_mcart_1 @ X11)))
% 0.20/0.49          | ~ (v1_relat_1 @ X12)
% 0.20/0.49          | ~ (r2_hidden @ X11 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.49        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.49        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(fc6_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.49        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.20/0.49         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '8'])).
% 0.20/0.49  thf(t20_mcart_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.49       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (((X8) != (k2_mcart_1 @ X8)) | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((k4_tarski @ X9 @ X10) != (k2_mcart_1 @ (k4_tarski @ X9 @ X10)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.49  thf(t7_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.49       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X13 : $i, X15 : $i]: ((k2_mcart_1 @ (k4_tarski @ X13 @ X15)) = (X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.49  thf('13', plain, (![X9 : $i, X10 : $i]: ((k4_tarski @ X9 @ X10) != (X10))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['9', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.49        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.20/0.49         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.49         (((X8) != (k1_mcart_1 @ X8)) | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         ((k4_tarski @ X9 @ X10) != (k1_mcart_1 @ (k4_tarski @ X9 @ X10)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X13 : $i, X14 : $i]: ((k1_mcart_1 @ (k4_tarski @ X13 @ X14)) = (X13))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.49  thf('21', plain, (![X9 : $i, X10 : $i]: ((k4_tarski @ X9 @ X10) != (X9))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['17', '21'])).
% 0.20/0.49  thf(fc11_relat_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49          | ~ (v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['17', '21'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf(t195_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.49               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((X6) = (k1_xboole_0))
% 0.20/0.49          | ((k2_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X7))
% 0.20/0.49          | ((X7) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (((((k2_relat_1 @ k1_xboole_0) = (sk_B))
% 0.20/0.49         | ((sk_B) = (k1_xboole_0))
% 0.20/0.49         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((((k2_relat_1 @ k1_xboole_0) = (sk_B)))
% 0.20/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['36', '37', '38'])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      ((((k1_xboole_0) = (sk_B))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.49      inference('sup+', [status(thm)], ['31', '39'])).
% 0.20/0.49  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.49      inference('split', [status(esa)], ['0'])).
% 0.20/0.49  thf('44', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 0.20/0.49  thf('45', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['14', '44'])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X6 : $i, X7 : $i]:
% 0.20/0.49         (((X6) = (k1_xboole_0))
% 0.20/0.49          | ((k2_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X7))
% 0.20/0.49          | ((X7) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X3 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X0)
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['46', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      ((((sk_A) = (k1_xboole_0))
% 0.20/0.49        | ((sk_B) = (k1_xboole_0))
% 0.20/0.49        | (v1_xboole_0 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.49  thf('50', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('51', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('52', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['49', '50', '51'])).
% 0.20/0.49  thf('53', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('54', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.49  thf('55', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('56', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
