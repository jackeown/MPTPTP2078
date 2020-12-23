%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Utfc0qDtO8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 213 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   13
%              Number of atoms          :  699 (5168 expanded)
%              Number of equality atoms :   99 ( 758 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t71_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = H ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = H ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l44_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ! [G: $i] :
                        ( ( m1_subset_1 @ G @ C )
                       => ( D
                         != ( k3_mcart_1 @ E @ F @ G ) ) ) ) )
            & ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( X8
        = ( k3_mcart_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('3',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6'])).

thf('9',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X8 @ X9 @ X7 @ X6 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ sk_B )
      | ( sk_E_1
       != ( k3_mcart_1 @ X18 @ X17 @ X19 ) )
      | ( sk_D = X19 )
      | ~ ( m1_subset_1 @ X19 @ sk_C )
      | ~ ( m1_subset_1 @ X18 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_D = X1 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X8 @ X9 @ X7 @ X6 ) @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('21',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X8 @ X9 @ X7 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('28',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['28','29','30','31'])).

thf('33',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','25','32'])).

thf('34',plain,
    ( sk_D
    = ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['7','34'])).

thf(t47_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ? [D: $i] :
            ( ? [E: $i,F: $i,G: $i] :
                ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                      = E )
                    & ( ( k6_mcart_1 @ A @ B @ C @ D )
                      = F )
                    & ( ( k7_mcart_1 @ A @ B @ C @ D )
                      = G ) )
                & ( D
                  = ( k3_mcart_1 @ E @ F @ G ) ) )
            & ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X15
       != ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
      | ( ( k7_mcart_1 @ X10 @ X11 @ X16 @ X15 )
        = X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) @ ( k3_zfmisc_1 @ X10 @ X11 @ X16 ) )
      | ( ( k7_mcart_1 @ X10 @ X11 @ X16 @ ( k3_mcart_1 @ X12 @ X13 @ X14 ) )
        = X14 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['7','34'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1 )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42','43','44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Utfc0qDtO8
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:35:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 28 iterations in 0.021s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.49  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.49  thf(t71_mcart_1, conjecture,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49       ( ( ![F:$i]:
% 0.21/0.49           ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.49             ( ![G:$i]:
% 0.21/0.49               ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.49                 ( ![H:$i]:
% 0.21/0.49                   ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.49                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.49                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.21/0.49         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.49        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49          ( ( ![F:$i]:
% 0.21/0.49              ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.49                ( ![G:$i]:
% 0.21/0.49                  ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.49                    ( ![H:$i]:
% 0.21/0.49                      ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.49                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.49                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.21/0.49            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.49              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(l44_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ?[D:$i]:
% 0.21/0.49            ( ( ![E:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.49                  ( ![F:$i]:
% 0.21/0.49                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.49                      ( ![G:$i]:
% 0.21/0.49                        ( ( m1_subset_1 @ G @ C ) =>
% 0.21/0.49                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.21/0.49              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X6) = (k1_xboole_0))
% 0.21/0.49          | ((X7) = (k1_xboole_0))
% 0.21/0.49          | ((X8)
% 0.21/0.49              = (k3_mcart_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ 
% 0.21/0.49                 (sk_F @ X8 @ X9 @ X7 @ X6) @ (sk_G @ X8 @ X9 @ X7 @ X6)))
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_E_1)
% 0.21/0.49            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49               (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X6) = (k1_xboole_0))
% 0.21/0.49          | ((X7) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_F @ X8 @ X9 @ X7 @ X6) @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X17 @ sk_B)
% 0.21/0.49          | ((sk_E_1) != (k3_mcart_1 @ X18 @ X17 @ X19))
% 0.21/0.49          | ((sk_D) = (X19))
% 0.21/0.49          | ~ (m1_subset_1 @ X19 @ sk_C)
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.49          | ((sk_D) = (X1))
% 0.21/0.49          | ((sk_E_1)
% 0.21/0.49              != (k3_mcart_1 @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((((sk_E_1) != (sk_E_1))
% 0.21/0.49        | ((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '17'])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X6) = (k1_xboole_0))
% 0.21/0.49          | ((X7) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_G @ X8 @ X9 @ X7 @ X6) @ X9)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['21', '22', '23', '24'])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (((X6) = (k1_xboole_0))
% 0.21/0.49          | ((X7) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_E @ X8 @ X9 @ X7 @ X6) @ X6)
% 0.21/0.49          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.49          | ((X9) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.49  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['28', '29', '30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      ((((sk_E_1) != (sk_E_1))
% 0.21/0.49        | ((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['18', '25', '32'])).
% 0.21/0.49  thf('34', plain, (((sk_D) = (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '34'])).
% 0.21/0.49  thf(t47_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49          ( ?[D:$i]:
% 0.21/0.49            ( ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.49                ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.49                       ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.49                       ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.49                  ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) & 
% 0.21/0.49              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.49         (((X10) = (k1_xboole_0))
% 0.21/0.49          | ((X11) = (k1_xboole_0))
% 0.21/0.49          | ((X15) != (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.49          | ((k7_mcart_1 @ X10 @ X11 @ X16 @ X15) = (X14))
% 0.21/0.49          | ~ (m1_subset_1 @ X15 @ (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.49          | ((X16) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.49         (((X16) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X13 @ X14) @ 
% 0.21/0.49               (k3_zfmisc_1 @ X10 @ X11 @ X16))
% 0.21/0.49          | ((k7_mcart_1 @ X10 @ X11 @ X16 @ (k3_mcart_1 @ X12 @ X13 @ X14))
% 0.21/0.49              = (X14))
% 0.21/0.49          | ((X11) = (k1_xboole_0))
% 0.21/0.49          | ((X10) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.49              (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49               (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D))
% 0.21/0.49              = (sk_D))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '37'])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['7', '34'])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1) = (sk_D))
% 0.21/0.49          | ((X0) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '40'])).
% 0.21/0.49  thf('42', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('46', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)],
% 0.21/0.49                ['41', '42', '43', '44', '45'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
