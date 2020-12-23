%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kWQhZjhlpc

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:47 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 189 expanded)
%              Number of leaves         :   19 (  67 expanded)
%              Depth                    :   16
%              Number of atoms          :  566 (1659 expanded)
%              Number of equality atoms :  108 ( 260 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t125_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C )
        = ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ( k2_zfmisc_1 @ X15 @ ( k4_xboole_0 @ X12 @ X14 ) )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X15 @ X12 ) @ ( k2_zfmisc_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('14',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19
       != ( k1_mcart_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k2_zfmisc_1 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k1_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ! [X0: $i] :
        ( ( ( k2_zfmisc_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
         != k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6','11'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('28',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['14'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19
       != ( k2_mcart_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k2_zfmisc_1 @ X18 @ X20 ) )
      | ( X20 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
     != ( k2_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( ( k2_zfmisc_1 @ sk_A @ ( k5_xboole_0 @ X0 @ X0 ) )
         != k1_xboole_0 )
        | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','36'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X12 @ X14 ) @ X13 )
      = ( k4_xboole_0 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t125_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 )
      = ( k5_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['40','48'])).

thf('50',plain,(
    sk_C
 != ( k2_mcart_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['14'])).

thf('52',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','47'])).

thf('55',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','53','54'])).

thf('56',plain,(
    $false ),
    inference(simplify,[status(thm)],['55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kWQhZjhlpc
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 78 iterations in 0.031s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(t66_mcart_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.22/0.49           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i]:
% 0.22/0.49        ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.49          ( ![C:$i]:
% 0.22/0.49            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.22/0.49              ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.22/0.49                ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t66_mcart_1])).
% 0.22/0.49  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.49  thf('1', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.49  thf(t100_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.49           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(t125_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( k2_zfmisc_1 @ C @ ( k4_xboole_0 @ A @ B ) ) =
% 0.22/0.49         ( k4_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.22/0.49       ( ( k2_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 0.22/0.49         ( k4_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ X15 @ (k4_xboole_0 @ X12 @ X14))
% 0.22/0.49           = (k4_xboole_0 @ (k2_zfmisc_1 @ X15 @ X12) @ 
% 0.22/0.49              (k2_zfmisc_1 @ X15 @ X14)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 0.22/0.49           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(t21_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X3 : $i, X4 : $i]:
% 0.22/0.49         ((k3_xboole_0 @ X3 @ (k2_xboole_0 @ X3 @ X4)) = (X3))),
% 0.22/0.49      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X1 : $i, X2 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X1 @ X2)
% 0.22/0.49           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.22/0.49           = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.49  thf(t46_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i]:
% 0.22/0.49         ((k4_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.22/0.49  thf('11', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6', '11'])).
% 0.22/0.49  thf('13', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain,
% 0.22/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['14'])).
% 0.22/0.49  thf('16', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t26_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![C:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.22/0.49                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.22/0.49                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X18) = (k1_xboole_0))
% 0.22/0.49          | ((X19) != (k1_mcart_1 @ X19))
% 0.22/0.49          | ~ (m1_subset_1 @ X19 @ (k2_zfmisc_1 @ X18 @ X20))
% 0.22/0.49          | ((X20) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      ((((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_C) != (k1_mcart_1 @ sk_C))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (((((sk_C) != (sk_C))
% 0.22/0.49         | ((sk_A) = (k1_xboole_0))
% 0.22/0.49         | ((sk_B) = (k1_xboole_0)))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.49  thf('21', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (((k2_zfmisc_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0))
% 0.22/0.49           | ((sk_A) = (k1_xboole_0))))
% 0.22/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['13', '22'])).
% 0.22/0.49  thf('24', plain,
% 0.22/0.49      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.49         <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['12', '23'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['5', '6', '11'])).
% 0.22/0.49  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('split', [status(esa)], ['14'])).
% 0.22/0.49  thf('29', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain,
% 0.22/0.49      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.49         (((X18) = (k1_xboole_0))
% 0.22/0.49          | ((X19) != (k2_mcart_1 @ X19))
% 0.22/0.49          | ~ (m1_subset_1 @ X19 @ (k2_zfmisc_1 @ X18 @ X20))
% 0.22/0.49          | ((X20) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.22/0.49  thf('31', plain,
% 0.22/0.49      ((((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_C) != (k2_mcart_1 @ sk_C))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (((((sk_C) != (sk_C))
% 0.22/0.49         | ((sk_A) = (k1_xboole_0))
% 0.22/0.49         | ((sk_B) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['28', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.49  thf('34', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.22/0.49         | ((sk_A) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain,
% 0.22/0.49      ((![X0 : $i]:
% 0.22/0.49          (((k2_zfmisc_1 @ sk_A @ (k5_xboole_0 @ X0 @ X0)) != (k1_xboole_0))
% 0.22/0.49           | ((sk_A) = (k1_xboole_0))))
% 0.22/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '35'])).
% 0.22/0.49  thf('37', plain,
% 0.22/0.49      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '36'])).
% 0.22/0.49  thf('38', plain,
% 0.22/0.49      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.49  thf('39', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.22/0.49         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.49  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ (k4_xboole_0 @ X12 @ X14) @ X13)
% 0.22/0.49           = (k4_xboole_0 @ (k2_zfmisc_1 @ X12 @ X13) @ 
% 0.22/0.49              (k2_zfmisc_1 @ X14 @ X13)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t125_zfmisc_1])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ (k4_xboole_0 @ X1 @ X1) @ X0)
% 0.22/0.49           = (k5_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.22/0.49      inference('sup+', [status(thm)], ['42', '43'])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((k2_zfmisc_1 @ (k5_xboole_0 @ X1 @ X1) @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['41', '47'])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      ((((k1_xboole_0) != (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.22/0.49      inference('demod', [status(thm)], ['40', '48'])).
% 0.22/0.49  thf('50', plain, (~ (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      ((((sk_C) = (k1_mcart_1 @ sk_C))) | (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.22/0.49      inference('split', [status(esa)], ['14'])).
% 0.22/0.49  thf('52', plain, ((((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.22/0.49      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.22/0.49  thf('53', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.49      inference('simpl_trail', [status(thm)], ['25', '52'])).
% 0.22/0.49  thf('54', plain,
% 0.22/0.49      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('sup+', [status(thm)], ['41', '47'])).
% 0.22/0.49  thf('55', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '53', '54'])).
% 0.22/0.49  thf('56', plain, ($false), inference('simplify', [status(thm)], ['55'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
