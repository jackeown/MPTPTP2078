%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nObcufoQF5

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:16 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 134 expanded)
%              Number of leaves         :   21 (  47 expanded)
%              Depth                    :   16
%              Number of atoms          :  473 (1023 expanded)
%              Number of equality atoms :   65 ( 155 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

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

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k4_tarski @ ( k1_mcart_1 @ X11 ) @ ( k2_mcart_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( ( sk_C
        = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ sk_C ) )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8
       != ( k2_mcart_1 @ X8 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('21',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != ( k2_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('22',plain,(
    ! [X13: $i,X15: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('23',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != X10 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','23'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('26',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('30',plain,
    ( ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) )
    | ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('31',plain,
    ( ( ( sk_C
        = ( k4_tarski @ sk_C @ ( k2_mcart_1 @ sk_C ) ) )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8
       != ( k1_mcart_1 @ X8 ) )
      | ( X8
       != ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != ( k1_mcart_1 @ ( k4_tarski @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_tarski @ X9 @ X10 )
     != X9 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k1_xboole_0
      = ( k2_zfmisc_1 @ sk_A @ sk_B ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('38',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['40','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['3','4'])).

thf('49',plain,(
    sk_C
 != ( k1_mcart_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('51',plain,
    ( sk_C
    = ( k2_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['28','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['44','45'])).

thf('54',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['5','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nObcufoQF5
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:49:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 46 iterations in 0.030s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(t8_boole, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t8_boole])).
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
% 0.19/0.48  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_xboole_0 @ sk_A)
% 0.19/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.48  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.48      inference('simplify_reflect+', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['6'])).
% 0.19/0.48  thf('8', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t2_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.48       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X4 : $i, X5 : $i]:
% 0.19/0.48         ((r2_hidden @ X4 @ X5)
% 0.19/0.48          | (v1_xboole_0 @ X5)
% 0.19/0.48          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.19/0.48      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.19/0.48        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.48  thf(t23_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ B ) =>
% 0.19/0.48       ( ( r2_hidden @ A @ B ) =>
% 0.19/0.48         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (((X11) = (k4_tarski @ (k1_mcart_1 @ X11) @ (k2_mcart_1 @ X11)))
% 0.19/0.48          | ~ (v1_relat_1 @ X12)
% 0.19/0.48          | ~ (r2_hidden @ X11 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.19/0.48  thf('12', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.19/0.48        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.19/0.48        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf(fc6_relat_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.19/0.48        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['12', '13'])).
% 0.19/0.48  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t8_boole])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.19/0.48        | ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ sk_C))
% 0.19/0.48         | ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.19/0.48         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['7', '18'])).
% 0.19/0.48  thf(t20_mcart_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.19/0.48       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (((X8) != (k2_mcart_1 @ X8)) | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.48  thf('21', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k4_tarski @ X9 @ X10) != (k2_mcart_1 @ (k4_tarski @ X9 @ X10)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.48  thf(t7_mcart_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.19/0.48       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X13 : $i, X15 : $i]: ((k2_mcart_1 @ (k4_tarski @ X13 @ X15)) = (X15))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('23', plain, (![X9 : $i, X10 : $i]: ((k4_tarski @ X9 @ X10) != (X10))),
% 0.19/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.48         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['19', '23'])).
% 0.19/0.48  thf(fc10_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.19/0.48       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X2)
% 0.19/0.48          | (v1_xboole_0 @ X3)
% 0.19/0.48          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v1_xboole_0 @ sk_A))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.48  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.19/0.48         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('split', [status(esa)], ['6'])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))
% 0.19/0.48        | ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['14', '17'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (((((sk_C) = (k4_tarski @ sk_C @ (k2_mcart_1 @ sk_C)))
% 0.19/0.48         | ((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))))
% 0.19/0.48         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['29', '30'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         (((X8) != (k1_mcart_1 @ X8)) | ((X8) != (k4_tarski @ X9 @ X10)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i]:
% 0.19/0.48         ((k4_tarski @ X9 @ X10) != (k1_mcart_1 @ (k4_tarski @ X9 @ X10)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i]: ((k1_mcart_1 @ (k4_tarski @ X13 @ X14)) = (X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.19/0.48  thf('35', plain, (![X9 : $i, X10 : $i]: ((k4_tarski @ X9 @ X10) != (X9))),
% 0.19/0.48      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.48         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['31', '35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         ((v1_xboole_0 @ X2)
% 0.19/0.48          | (v1_xboole_0 @ X3)
% 0.19/0.48          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 0.19/0.48      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48         | (v1_xboole_0 @ sk_B)
% 0.19/0.48         | (v1_xboole_0 @ sk_A))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.19/0.48  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('40', plain,
% 0.19/0.48      ((((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.19/0.48         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('demod', [status(thm)], ['38', '39'])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t8_boole])).
% 0.19/0.48  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_xboole_0 @ sk_B)
% 0.19/0.48          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.48  thf('44', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 0.19/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.48  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('46', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('simplify_reflect+', [status(thm)], ['44', '45'])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_A)) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.19/0.48      inference('clc', [status(thm)], ['40', '46'])).
% 0.19/0.48  thf('48', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.48      inference('simplify_reflect+', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf('49', plain, (~ (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      ((((sk_C) = (k2_mcart_1 @ sk_C))) | (((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('split', [status(esa)], ['6'])).
% 0.19/0.48  thf('51', plain, ((((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.19/0.48  thf('52', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['28', '51'])).
% 0.19/0.48  thf('53', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.19/0.48      inference('simplify_reflect+', [status(thm)], ['44', '45'])).
% 0.19/0.48  thf('54', plain, ((v1_xboole_0 @ sk_A)),
% 0.19/0.48      inference('clc', [status(thm)], ['52', '53'])).
% 0.19/0.48  thf('55', plain, ($false), inference('demod', [status(thm)], ['5', '54'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
