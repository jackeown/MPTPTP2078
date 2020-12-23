%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pihj3vD29J

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 306 expanded)
%              Number of leaves         :   17 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  812 (7643 expanded)
%              Number of equality atoms :  104 (1107 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_1_type,type,(
    sk_G_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t70_mcart_1,conjecture,(
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
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20
        = ( k3_mcart_1 @ ( sk_E @ X20 @ X21 @ X19 @ X18 ) @ ( sk_F_1 @ X20 @ X21 @ X19 @ X18 ) @ ( sk_G_1 @ X20 @ X21 @ X19 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('3',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
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
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6'])).

thf('8',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6'])).

thf('9',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F_1 @ X20 @ X21 @ X19 @ X18 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
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
    m1_subset_1 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ( sk_D = X22 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X23 @ X22 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ( sk_D
        = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G_1 @ X20 @ X21 @ X19 @ X18 ) @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('21',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
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
    m1_subset_1 @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X20 @ X21 @ X19 @ X18 ) @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
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
      = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','25','32'])).

thf('34',plain,
    ( sk_D
    = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','34'])).

thf(d6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ! [E: $i] :
                  ( ( m1_subset_1 @ E @ B )
                 => ( ( E
                      = ( k6_mcart_1 @ A @ B @ C @ D ) )
                  <=> ! [F: $i,G: $i,H: $i] :
                        ( ( D
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( E = G ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( X8
       != ( k6_mcart_1 @ X6 @ X7 @ X9 @ X10 ) )
      | ( X8 = X11 )
      | ( X10
       != ( k3_mcart_1 @ X12 @ X11 @ X13 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d6_mcart_1])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X9: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X12 @ X11 @ X13 ) @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( ( k6_mcart_1 @ X6 @ X7 @ X9 @ ( k3_mcart_1 @ X12 @ X11 @ X13 ) )
        = X11 )
      | ~ ( m1_subset_1 @ ( k6_mcart_1 @ X6 @ X7 @ X9 @ ( k3_mcart_1 @ X12 @ X11 @ X13 ) ) @ X7 )
      | ( X7 = k1_xboole_0 )
      | ( X6 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) @ X1 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','34'])).

thf('40',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','34'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1 ) @ X1 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1 )
        = sk_D )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = sk_D )
    | ~ ( m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k6_mcart_1 @ X14 @ X15 @ X16 @ X17 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_mcart_1])).

thf('45',plain,(
    m1_subset_1 @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = sk_D )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47','48','49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Pihj3vD29J
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 34 iterations in 0.024s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.50  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_G_1_type, type, sk_G_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(t70_mcart_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50       ( ( ![F:$i]:
% 0.22/0.50           ( ( m1_subset_1 @ F @ A ) =>
% 0.22/0.50             ( ![G:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ G @ B ) =>
% 0.22/0.50                 ( ![H:$i]:
% 0.22/0.50                   ( ( m1_subset_1 @ H @ C ) =>
% 0.22/0.50                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.50                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.22/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.50        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50          ( ( ![F:$i]:
% 0.22/0.50              ( ( m1_subset_1 @ F @ A ) =>
% 0.22/0.50                ( ![G:$i]:
% 0.22/0.50                  ( ( m1_subset_1 @ G @ B ) =>
% 0.22/0.50                    ( ![H:$i]:
% 0.22/0.50                      ( ( m1_subset_1 @ H @ C ) =>
% 0.22/0.50                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.50                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.22/0.50            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(l44_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ?[D:$i]:
% 0.22/0.50            ( ( ![E:$i]:
% 0.22/0.50                ( ( m1_subset_1 @ E @ A ) =>
% 0.22/0.50                  ( ![F:$i]:
% 0.22/0.50                    ( ( m1_subset_1 @ F @ B ) =>
% 0.22/0.50                      ( ![G:$i]:
% 0.22/0.50                        ( ( m1_subset_1 @ G @ C ) =>
% 0.22/0.50                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.22/0.50              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.50         (((X18) = (k1_xboole_0))
% 0.22/0.50          | ((X19) = (k1_xboole_0))
% 0.22/0.50          | ((X20)
% 0.22/0.50              = (k3_mcart_1 @ (sk_E @ X20 @ X21 @ X19 @ X18) @ 
% 0.22/0.50                 (sk_F_1 @ X20 @ X21 @ X19 @ X18) @ 
% 0.22/0.50                 (sk_G_1 @ X20 @ X21 @ X19 @ X18)))
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.22/0.50          | ((X21) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((((sk_C) = (k1_xboole_0))
% 0.22/0.50        | ((sk_E_1)
% 0.22/0.50            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.50               (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.50               (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.22/0.50        | ((sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('6', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (((sk_E_1)
% 0.22/0.50         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.50            (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.50            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (((sk_E_1)
% 0.22/0.50         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.50            (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.22/0.50            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.50         (((X18) = (k1_xboole_0))
% 0.22/0.50          | ((X19) = (k1_xboole_0))
% 0.22/0.50          | (m1_subset_1 @ (sk_F_1 @ X20 @ X21 @ X19 @ X18) @ X19)
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.22/0.50          | ((X21) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((((sk_C) = (k1_xboole_0))
% 0.22/0.50        | (m1_subset_1 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.22/0.50        | ((sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((m1_subset_1 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.22/0.50          | ((sk_D) = (X22))
% 0.22/0.50          | ((sk_E_1) != (k3_mcart_1 @ X23 @ X22 @ X24))
% 0.22/0.50          | ~ (m1_subset_1 @ X24 @ sk_C)
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.50          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.22/0.50          | ((sk_E_1)
% 0.22/0.50              != (k3_mcart_1 @ X0 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1))
% 0.22/0.50          | ((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      ((((sk_E_1) != (sk_E_1))
% 0.22/0.50        | ((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.22/0.50        | ~ (m1_subset_1 @ (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.22/0.50        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '17'])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.50         (((X18) = (k1_xboole_0))
% 0.22/0.50          | ((X19) = (k1_xboole_0))
% 0.22/0.50          | (m1_subset_1 @ (sk_G_1 @ X20 @ X21 @ X19 @ X18) @ X21)
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.22/0.50          | ((X21) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((((sk_C) = (k1_xboole_0))
% 0.22/0.50        | (m1_subset_1 @ (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.22/0.50        | ((sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      ((m1_subset_1 @ (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['21', '22', '23', '24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.50         (((X18) = (k1_xboole_0))
% 0.22/0.50          | ((X19) = (k1_xboole_0))
% 0.22/0.50          | (m1_subset_1 @ (sk_E @ X20 @ X21 @ X19 @ X18) @ X18)
% 0.22/0.50          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.22/0.50          | ((X21) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((sk_C) = (k1_xboole_0))
% 0.22/0.50        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.22/0.50        | ((sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('31', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['28', '29', '30', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      ((((sk_E_1) != (sk_E_1))
% 0.22/0.50        | ((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '25', '32'])).
% 0.22/0.50  thf('34', plain, (((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.50      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((sk_E_1)
% 0.22/0.50         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.22/0.50            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '34'])).
% 0.22/0.50  thf(d6_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ~( ![D:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50                 ( ![E:$i]:
% 0.22/0.50                   ( ( m1_subset_1 @ E @ B ) =>
% 0.22/0.50                     ( ( ( E ) = ( k6_mcart_1 @ A @ B @ C @ D ) ) <=>
% 0.22/0.50                       ( ![F:$i,G:$i,H:$i]:
% 0.22/0.50                         ( ( ( D ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.22/0.50                           ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, 
% 0.22/0.50         X13 : $i]:
% 0.22/0.50         (((X6) = (k1_xboole_0))
% 0.22/0.50          | ((X7) = (k1_xboole_0))
% 0.22/0.50          | ~ (m1_subset_1 @ X8 @ X7)
% 0.22/0.50          | ((X8) != (k6_mcart_1 @ X6 @ X7 @ X9 @ X10))
% 0.22/0.50          | ((X8) = (X11))
% 0.22/0.50          | ((X10) != (k3_mcart_1 @ X12 @ X11 @ X13))
% 0.22/0.50          | ~ (m1_subset_1 @ X10 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.22/0.50          | ((X9) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d6_mcart_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i, X9 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (((X9) = (k1_xboole_0))
% 0.22/0.50          | ~ (m1_subset_1 @ (k3_mcart_1 @ X12 @ X11 @ X13) @ 
% 0.22/0.50               (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.22/0.50          | ((k6_mcart_1 @ X6 @ X7 @ X9 @ (k3_mcart_1 @ X12 @ X11 @ X13))
% 0.22/0.50              = (X11))
% 0.22/0.50          | ~ (m1_subset_1 @ 
% 0.22/0.50               (k6_mcart_1 @ X6 @ X7 @ X9 @ (k3_mcart_1 @ X12 @ X11 @ X13)) @ 
% 0.22/0.50               X7)
% 0.22/0.50          | ((X7) = (k1_xboole_0))
% 0.22/0.50          | ((X6) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.50          | ((X2) = (k1_xboole_0))
% 0.22/0.50          | ((X1) = (k1_xboole_0))
% 0.22/0.50          | ~ (m1_subset_1 @ 
% 0.22/0.50               (k6_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.22/0.50                (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.22/0.50                 (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))) @ 
% 0.22/0.50               X1)
% 0.22/0.50          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.22/0.50              (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.22/0.50               (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.22/0.50              = (sk_D))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (((sk_E_1)
% 0.22/0.50         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.22/0.50            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '34'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (((sk_E_1)
% 0.22/0.50         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.22/0.50            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '34'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.50          | ((X2) = (k1_xboole_0))
% 0.22/0.50          | ((X1) = (k1_xboole_0))
% 0.22/0.50          | ~ (m1_subset_1 @ (k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1) @ X1)
% 0.22/0.50          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1) = (sk_D))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      ((((sk_C) = (k1_xboole_0))
% 0.22/0.50        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))
% 0.22/0.50        | ~ (m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ sk_B)
% 0.22/0.50        | ((sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k6_mcart_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.50       ( m1_subset_1 @ ( k6_mcart_1 @ A @ B @ C @ D ) @ B ) ))).
% 0.22/0.50  thf('44', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.50         ((m1_subset_1 @ (k6_mcart_1 @ X14 @ X15 @ X16 @ X17) @ X15)
% 0.22/0.50          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X14 @ X15 @ X16)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k6_mcart_1])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      ((m1_subset_1 @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) @ sk_B)),
% 0.22/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((((sk_C) = (k1_xboole_0))
% 0.22/0.50        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))
% 0.22/0.50        | ((sk_B) = (k1_xboole_0))
% 0.22/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '45'])).
% 0.22/0.50  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('49', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('51', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)],
% 0.22/0.50                ['46', '47', '48', '49', '50'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
