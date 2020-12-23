%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RXusrWcPRj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 215 expanded)
%              Number of leaves         :   18 (  73 expanded)
%              Depth                    :   14
%              Number of atoms          :  724 (5218 expanded)
%              Number of equality atoms :   99 ( 758 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t69_mcart_1,conjecture,(
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
                     => ( D = F ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = F ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_mcart_1])).

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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( X5
        = ( k3_mcart_1 @ ( sk_E @ X5 @ X6 @ X4 @ X3 ) @ ( sk_F @ X5 @ X6 @ X4 @ X3 ) @ ( sk_G @ X5 @ X6 @ X4 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X5 @ ( k3_zfmisc_1 @ X3 @ X4 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X5 @ X6 @ X4 @ X3 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k3_zfmisc_1 @ X3 @ X4 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ sk_B )
      | ( sk_D = X15 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X15 @ X14 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ sk_C )
      | ~ ( m1_subset_1 @ X15 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_D
      = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X5 @ X6 @ X4 @ X3 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k3_zfmisc_1 @ X3 @ X4 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('22',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['22','23','24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_D
      = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X5 @ X6 @ X4 @ X3 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k3_zfmisc_1 @ X3 @ X4 @ X6 ) )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('30',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['30','31','32','33'])).

thf('35',plain,
    ( sk_D
    = ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['27','34'])).

thf('36',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','35'])).

thf(t68_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ? [E: $i,F: $i,G: $i] :
              ( ~ ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                    = E )
                  & ( ( k6_mcart_1 @ A @ B @ C @ D )
                    = F )
                  & ( ( k7_mcart_1 @ A @ B @ C @ D )
                    = G ) )
              & ( D
                = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) )).

thf('37',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X9 @ X8 @ X7 ) )
      | ( ( k5_mcart_1 @ X9 @ X8 @ X7 @ X10 )
        = X11 )
      | ( X10
       != ( k3_mcart_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t68_mcart_1])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( k5_mcart_1 @ X9 @ X8 @ X7 @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) )
        = X11 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X11 @ X12 @ X13 ) @ ( k3_zfmisc_1 @ X9 @ X8 @ X7 ) )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ sk_D @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','35'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RXusrWcPRj
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:02:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 24 iterations in 0.018s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(t69_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47       ( ( ![F:$i]:
% 0.20/0.47           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.47             ( ![G:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.47                 ( ![H:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.47                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.47                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47          ( ( ![F:$i]:
% 0.20/0.47              ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.47                ( ![G:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ G @ B ) =>
% 0.20/0.47                    ( ![H:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @ H @ C ) =>
% 0.20/0.47                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.20/0.47                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(l44_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ?[D:$i]:
% 0.20/0.47            ( ( ![E:$i]:
% 0.20/0.47                ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.47                  ( ![F:$i]:
% 0.20/0.47                    ( ( m1_subset_1 @ F @ B ) =>
% 0.20/0.47                      ( ![G:$i]:
% 0.20/0.47                        ( ( m1_subset_1 @ G @ C ) =>
% 0.20/0.47                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.20/0.47              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((X3) = (k1_xboole_0))
% 0.20/0.47          | ((X4) = (k1_xboole_0))
% 0.20/0.47          | ((X5)
% 0.20/0.47              = (k3_mcart_1 @ (sk_E @ X5 @ X6 @ X4 @ X3) @ 
% 0.20/0.47                 (sk_F @ X5 @ X6 @ X4 @ X3) @ (sk_G @ X5 @ X6 @ X4 @ X3)))
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k3_zfmisc_1 @ X3 @ X4 @ X6))
% 0.20/0.47          | ((X6) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_E_1)
% 0.20/0.47            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47               (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.47  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (((sk_E_1)
% 0.20/0.47         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (((sk_E_1)
% 0.20/0.47         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47            (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6'])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((X3) = (k1_xboole_0))
% 0.20/0.47          | ((X4) = (k1_xboole_0))
% 0.20/0.47          | (m1_subset_1 @ (sk_F @ X5 @ X6 @ X4 @ X3) @ X4)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k3_zfmisc_1 @ X3 @ X4 @ X6))
% 0.20/0.47          | ((X6) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((((sk_C) = (k1_xboole_0))
% 0.20/0.47        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X14 @ sk_B)
% 0.20/0.47          | ((sk_D) = (X15))
% 0.20/0.47          | ((sk_E_1) != (k3_mcart_1 @ X15 @ X14 @ X16))
% 0.20/0.47          | ~ (m1_subset_1 @ X16 @ sk_C)
% 0.20/0.47          | ~ (m1_subset_1 @ X15 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.47          | ((sk_E_1)
% 0.20/0.47              != (k3_mcart_1 @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1))
% 0.20/0.47          | ((sk_D) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      ((((sk_E_1) != (sk_E_1))
% 0.20/0.47        | ((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.20/0.47        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.47        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['8', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.47        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.47        | ((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((X3) = (k1_xboole_0))
% 0.20/0.47          | ((X4) = (k1_xboole_0))
% 0.20/0.47          | (m1_subset_1 @ (sk_G @ X5 @ X6 @ X4 @ X3) @ X6)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k3_zfmisc_1 @ X3 @ X4 @ X6))
% 0.20/0.47          | ((X6) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      ((((sk_C) = (k1_xboole_0))
% 0.20/0.47        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.47        | ((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['19', '26'])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.47         (((X3) = (k1_xboole_0))
% 0.20/0.47          | ((X4) = (k1_xboole_0))
% 0.20/0.47          | (m1_subset_1 @ (sk_E @ X5 @ X6 @ X4 @ X3) @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k3_zfmisc_1 @ X3 @ X4 @ X6))
% 0.20/0.47          | ((X6) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      ((((sk_C) = (k1_xboole_0))
% 0.20/0.47        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.47  thf('31', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['30', '31', '32', '33'])).
% 0.20/0.47  thf('35', plain, (((sk_D) = (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '34'])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (((sk_E_1)
% 0.20/0.47         = (k3_mcart_1 @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '35'])).
% 0.20/0.47  thf(t68_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.47       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47            ( ?[E:$i,F:$i,G:$i]:
% 0.20/0.47              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.20/0.47                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.20/0.47                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.20/0.47                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (((X7) = (k1_xboole_0))
% 0.20/0.47          | ((X8) = (k1_xboole_0))
% 0.20/0.47          | ((X9) = (k1_xboole_0))
% 0.20/0.47          | ~ (m1_subset_1 @ X10 @ (k3_zfmisc_1 @ X9 @ X8 @ X7))
% 0.20/0.47          | ((k5_mcart_1 @ X9 @ X8 @ X7 @ X10) = (X11))
% 0.20/0.47          | ((X10) != (k3_mcart_1 @ X11 @ X12 @ X13)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t68_mcart_1])).
% 0.20/0.47  thf('38', plain,
% 0.20/0.47      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.47         (((k5_mcart_1 @ X9 @ X8 @ X7 @ (k3_mcart_1 @ X11 @ X12 @ X13)) = (X11))
% 0.20/0.47          | ~ (m1_subset_1 @ (k3_mcart_1 @ X11 @ X12 @ X13) @ 
% 0.20/0.47               (k3_zfmisc_1 @ X9 @ X8 @ X7))
% 0.20/0.47          | ((X9) = (k1_xboole_0))
% 0.20/0.47          | ((X8) = (k1_xboole_0))
% 0.20/0.47          | ((X7) = (k1_xboole_0)))),
% 0.20/0.47      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.47  thf('39', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0))
% 0.20/0.47          | ((X1) = (k1_xboole_0))
% 0.20/0.47          | ((X2) = (k1_xboole_0))
% 0.20/0.47          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.20/0.47              (k3_mcart_1 @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.20/0.47              = (sk_D)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['36', '38'])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (((sk_E_1)
% 0.20/0.47         = (k3_mcart_1 @ sk_D @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.20/0.47            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['7', '35'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.47          | ((X0) = (k1_xboole_0))
% 0.20/0.47          | ((X1) = (k1_xboole_0))
% 0.20/0.47          | ((X2) = (k1_xboole_0))
% 0.20/0.47          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1) = (sk_D)))),
% 0.20/0.47      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      ((((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '41'])).
% 0.20/0.47  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('46', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain, ($false),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['42', '43', '44', '45', '46'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
