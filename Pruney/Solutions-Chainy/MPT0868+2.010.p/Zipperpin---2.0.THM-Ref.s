%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BqmoEAtXaq

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 315 expanded)
%              Number of leaves         :   20 (  98 expanded)
%              Depth                    :   22
%              Number of atoms          :  509 (3013 expanded)
%              Number of equality atoms :   78 ( 471 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ( X10
        = ( k4_tarski @ ( k1_mcart_1 @ X10 ) @ ( k2_mcart_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
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
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k2_mcart_1 @ X7 ) )
      | ( X7
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_tarski @ X8 @ X9 )
     != ( k2_mcart_1 @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('12',plain,(
    ! [X12: $i,X14: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X12 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_tarski @ X8 @ X9 )
     != X9 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','13'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('19',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X7
       != ( k1_mcart_1 @ X7 ) )
      | ( X7
       != ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_tarski @ X8 @ X9 )
     != ( k1_mcart_1 @ ( k4_tarski @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_tarski @ X8 @ X9 )
     != X8 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('28',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','23'])).

thf('30',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('31',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','42'])).

thf('44',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('45',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','13'])).

thf('47',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('48',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_xboole_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('57',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BqmoEAtXaq
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 48 iterations in 0.018s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(t26_mcart_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46          ( ~( ![C:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.46                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.46                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.46             ( ~( ![C:$i]:
% 0.20/0.46                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.46                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.46                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t2_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i]:
% 0.20/0.46         ((r2_hidden @ X3 @ X4)
% 0.20/0.46          | (v1_xboole_0 @ X4)
% 0.20/0.46          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.46  thf(t23_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.46         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X10 : $i, X11 : $i]:
% 0.20/0.46         (((X10) = (k4_tarski @ (k1_mcart_1 @ X10) @ (k2_mcart_1 @ X10)))
% 0.20/0.46          | ~ (v1_relat_1 @ X11)
% 0.20/0.46          | ~ (r2_hidden @ X10 @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.46  thf(fc6_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.20/0.46         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.46         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['1', '8'])).
% 0.20/0.46  thf(t20_mcart_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.46       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.46         (((X7) != (k2_mcart_1 @ X7)) | ((X7) != (k4_tarski @ X8 @ X9)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         ((k4_tarski @ X8 @ X9) != (k2_mcart_1 @ (k4_tarski @ X8 @ X9)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.46  thf(t7_mcart_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.46       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X12 : $i, X14 : $i]: ((k2_mcart_1 @ (k4_tarski @ X12 @ X14)) = (X14))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('13', plain, (![X8 : $i, X9 : $i]: ((k4_tarski @ X8 @ X9) != (X9))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['9', '13'])).
% 0.20/0.46  thf(l13_xboole_0, axiom,
% 0.20/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.46        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.20/0.46         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.46         (((X7) != (k1_mcart_1 @ X7)) | ((X7) != (k4_tarski @ X8 @ X9)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i]:
% 0.20/0.46         ((k4_tarski @ X8 @ X9) != (k1_mcart_1 @ (k4_tarski @ X8 @ X9)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X12 : $i, X13 : $i]: ((k1_mcart_1 @ (k4_tarski @ X12 @ X13)) = (X12))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.46  thf('23', plain, (![X8 : $i, X9 : $i]: ((k4_tarski @ X8 @ X9) != (X8))),
% 0.20/0.46      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['19', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf(fc10_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.20/0.46       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         ((v1_xboole_0 @ X1)
% 0.20/0.46          | (v1_xboole_0 @ X2)
% 0.20/0.46          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46         | (v1_xboole_0 @ sk_B)
% 0.20/0.46         | (v1_xboole_0 @ sk_A))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['19', '23'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (((v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('demod', [status(thm)], ['28', '31'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      ((((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.46         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.46  thf('35', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (((v1_xboole_0 @ sk_A)) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.46  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('40', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.20/0.46  thf('41', plain,
% 0.20/0.46      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('42', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.46  thf('43', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['16', '42'])).
% 0.20/0.46  thf('44', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         ((v1_xboole_0 @ X1)
% 0.20/0.46          | (v1_xboole_0 @ X2)
% 0.20/0.46          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.20/0.46  thf('45', plain,
% 0.20/0.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.46        | (v1_xboole_0 @ sk_B)
% 0.20/0.46        | (v1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.46  thf('46', plain,
% 0.20/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.46         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['9', '13'])).
% 0.20/0.46  thf('47', plain,
% 0.20/0.46      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.46         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('48', plain,
% 0.20/0.46      (((v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.46      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.46  thf('49', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.46  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['48', '49'])).
% 0.20/0.46  thf('51', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['45', '50'])).
% 0.20/0.46  thf('52', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('53', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.46  thf('54', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('55', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.20/0.46  thf('56', plain,
% 0.20/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.46  thf('57', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['55', '56'])).
% 0.20/0.46  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('59', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
