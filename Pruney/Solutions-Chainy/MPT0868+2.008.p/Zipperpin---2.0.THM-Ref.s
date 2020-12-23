%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OB3pOxZ1uw

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 272 expanded)
%              Number of leaves         :   23 (  88 expanded)
%              Depth                    :   19
%              Number of atoms          :  526 (2500 expanded)
%              Number of equality atoms :   88 ( 409 expanded)
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

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

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
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

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
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
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
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X6 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('36',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = sk_A )
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
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( k1_xboole_0 = sk_A )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['31','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
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
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('49',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['14','44'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('52',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) )
        = X6 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('54',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

thf('58',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['49','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OB3pOxZ1uw
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:32:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 66 iterations in 0.050s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(t26_mcart_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ![C:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.51                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.51                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51             ( ~( ![C:$i]:
% 0.20/0.51                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.51                    ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.51                      ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t26_mcart_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i]:
% 0.20/0.51         ((r2_hidden @ X1 @ X2)
% 0.20/0.51          | (v1_xboole_0 @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t23_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.51         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (((X11) = (k4_tarski @ (k1_mcart_1 @ X11) @ (k2_mcart_1 @ X11)))
% 0.20/0.51          | ~ (v1_relat_1 @ X12)
% 0.20/0.51          | ~ (r2_hidden @ X11 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.20/0.51         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.51         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['1', '8'])).
% 0.20/0.51  thf(t20_mcart_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.51       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (((X8) != (k2_mcart_1 @ X8)) | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((k4_tarski @ X9 @ X10) != (k2_mcart_1 @ (k4_tarski @ X9 @ X10)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.20/0.51  thf(t7_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X13 : $i, X15 : $i]: ((k2_mcart_1 @ (k4_tarski @ X13 @ X15)) = (X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.51  thf('13', plain, (![X9 : $i, X10 : $i]: ((k4_tarski @ X9 @ X10) != (X10))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['9', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.51        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.20/0.51         | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.20/0.51         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         (((X8) != (k1_mcart_1 @ X8)) | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         ((k4_tarski @ X9 @ X10) != (k1_mcart_1 @ (k4_tarski @ X9 @ X10)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i]: ((k1_mcart_1 @ (k4_tarski @ X13 @ X14)) = (X13))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.51  thf('21', plain, (![X9 : $i, X10 : $i]: ((k4_tarski @ X9 @ X10) != (X9))),
% 0.20/0.51      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['17', '21'])).
% 0.20/0.51  thf(fc10_relat_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X3 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X3 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X3)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ k1_xboole_0)
% 0.20/0.51          | ~ (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 0.20/0.51         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.51         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['17', '21'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.20/0.51         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.51  thf(t195_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.20/0.51               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (((X6) = (k1_xboole_0))
% 0.20/0.51          | ((k1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X6))
% 0.20/0.51          | ((X7) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 0.20/0.51         | ((sk_B) = (k1_xboole_0))
% 0.20/0.51         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k1_relat_1 @ k1_xboole_0) = (sk_A)))
% 0.20/0.51         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['36', '37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((((k1_xboole_0) = (sk_A))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['31', '39'])).
% 0.20/0.51  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('42', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('44', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 0.20/0.51  thf('45', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['14', '44'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.51  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('49', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['14', '44'])).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('52', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (((X6) = (k1_xboole_0))
% 0.20/0.51          | ((k1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7)) = (X6))
% 0.20/0.51          | ((X7) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((((k1_relat_1 @ k1_xboole_0) = (sk_A))
% 0.20/0.51        | ((sk_B) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['52', '53'])).
% 0.20/0.51  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 0.20/0.51  thf('58', plain, (((k1_xboole_0) = (sk_A))),
% 0.20/0.51      inference('sup+', [status(thm)], ['49', '57'])).
% 0.20/0.51  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('60', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
