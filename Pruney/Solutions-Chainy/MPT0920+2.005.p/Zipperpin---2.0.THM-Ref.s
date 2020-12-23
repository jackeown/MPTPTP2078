%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SxvvdXUajy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  110 (2423 expanded)
%              Number of leaves         :   21 ( 739 expanded)
%              Depth                    :   23
%              Number of atoms          : 1537 (78186 expanded)
%              Number of equality atoms :  202 (10948 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t80_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = H ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = H ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l68_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ? [E: $i] :
            ( ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ B )
                   => ! [H: $i] :
                        ( ( m1_subset_1 @ H @ C )
                       => ! [I: $i] :
                            ( ( m1_subset_1 @ I @ D )
                           => ( E
                             != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )
            & ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14
        = ( k4_mcart_1 @ ( sk_F @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_G @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_H @ X14 @ X15 @ X13 @ X12 @ X11 ) @ ( sk_I @ X14 @ X15 @ X13 @ X12 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('3',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 )
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

thf('7',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6','7'])).

thf('9',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['3','4','5','6','7'])).

thf('10',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('12',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15','16'])).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ sk_B )
      | ~ ( m1_subset_1 @ X26 @ sk_D )
      | ( sk_F_1
       != ( k4_mcart_1 @ X27 @ X25 @ X28 @ X26 ) )
      | ( sk_E = X25 )
      | ~ ( m1_subset_1 @ X28 @ sk_C )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
        = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('23',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('31',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X14 @ X15 @ X13 @ X12 @ X11 ) @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('39',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42','43'])).

thf('45',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','28','36','44'])).

thf('46',plain,
    ( sk_E
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','46'])).

thf(t78_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ? [F: $i,G: $i,H: $i,I: $i] :
              ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                    = F )
                  & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                    = G )
                  & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                    = H )
                  & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                    = I ) )
              & ( E
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( ( k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20 )
        = X21 )
      | ( X20
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('51',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) )
        = X21 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','46'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['47','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['47','60'])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( ( k10_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20 )
        = X24 )
      | ( X20
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('65',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k10_mcart_1 @ X19 @ X18 @ X17 @ X16 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) )
        = X24 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) )
        = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','65'])).

thf('67',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['47','60'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['69','70','71','72','73'])).

thf('75',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['61','74'])).

thf('76',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( ( k9_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20 )
        = X23 )
      | ( X20
       != ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( ( k9_mcart_1 @ X19 @ X18 @ X17 @ X16 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) )
        = X23 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X22 @ X23 @ X24 @ X21 ) @ ( k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16 ) )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['61','74'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','80'])).

thf('82',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['81','82','83','84','85','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SxvvdXUajy
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:00:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 77 iterations in 0.051s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(t80_mcart_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( ( ![G:$i]:
% 0.21/0.50           ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.50             ( ![H:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.50                 ( ![I:$i]:
% 0.21/0.50                   ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.50                     ( ![J:$i]:
% 0.21/0.50                       ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.50                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.50                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.50        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50          ( ( ![G:$i]:
% 0.21/0.50              ( ( m1_subset_1 @ G @ A ) =>
% 0.21/0.50                ( ![H:$i]:
% 0.21/0.50                  ( ( m1_subset_1 @ H @ B ) =>
% 0.21/0.50                    ( ![I:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @ I @ C ) =>
% 0.21/0.50                        ( ![J:$i]:
% 0.21/0.50                          ( ( m1_subset_1 @ J @ D ) =>
% 0.21/0.50                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.21/0.50                              ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.50            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50              ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t80_mcart_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(l68_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ?[E:$i]:
% 0.21/0.50            ( ( ![F:$i]:
% 0.21/0.50                ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.50                  ( ![G:$i]:
% 0.21/0.50                    ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.50                      ( ![H:$i]:
% 0.21/0.50                        ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.50                          ( ![I:$i]:
% 0.21/0.50                            ( ( m1_subset_1 @ I @ D ) =>
% 0.21/0.50                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.21/0.50              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (((X11) = (k1_xboole_0))
% 0.21/0.50          | ((X12) = (k1_xboole_0))
% 0.21/0.50          | ((X13) = (k1_xboole_0))
% 0.21/0.50          | ((X14)
% 0.21/0.50              = (k4_mcart_1 @ (sk_F @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.21/0.50                 (sk_G @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.21/0.50                 (sk_H @ X14 @ X15 @ X13 @ X12 @ X11) @ 
% 0.21/0.50                 (sk_I @ X14 @ X15 @ X13 @ X12 @ X11)))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.50          | ((X15) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((sk_F_1)
% 0.21/0.50            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (((X11) = (k1_xboole_0))
% 0.21/0.50          | ((X12) = (k1_xboole_0))
% 0.21/0.50          | ((X13) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_G @ X14 @ X15 @ X13 @ X12 @ X11) @ X12)
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.50          | ((X15) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['12', '13', '14', '15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X25 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ sk_D)
% 0.21/0.50          | ((sk_F_1) != (k4_mcart_1 @ X27 @ X25 @ X28 @ X26))
% 0.21/0.50          | ((sk_E) = (X25))
% 0.21/0.50          | ~ (m1_subset_1 @ X28 @ sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.50          | ((sk_E) = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.50          | ((sk_F_1)
% 0.21/0.50              != (k4_mcart_1 @ X0 @ 
% 0.21/0.50                  (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((((sk_F_1) != (sk_F_1))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.50        | ((sk_E) = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (((X11) = (k1_xboole_0))
% 0.21/0.50          | ((X12) = (k1_xboole_0))
% 0.21/0.50          | ((X13) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_I @ X14 @ X15 @ X13 @ X12 @ X11) @ X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.50          | ((X15) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['23', '24', '25', '26', '27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (((X11) = (k1_xboole_0))
% 0.21/0.50          | ((X12) = (k1_xboole_0))
% 0.21/0.50          | ((X13) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_H @ X14 @ X15 @ X13 @ X12 @ X11) @ X13)
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.50          | ((X15) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['31', '32', '33', '34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         (((X11) = (k1_xboole_0))
% 0.21/0.50          | ((X12) = (k1_xboole_0))
% 0.21/0.50          | ((X13) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_F @ X14 @ X15 @ X13 @ X12 @ X11) @ X11)
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X11 @ X12 @ X13 @ X15))
% 0.21/0.50          | ((X15) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['39', '40', '41', '42', '43'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((((sk_F_1) != (sk_F_1))
% 0.21/0.50        | ((sk_E) = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['20', '28', '36', '44'])).
% 0.21/0.50  thf('46', plain, (((sk_E) = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '46'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '46'])).
% 0.21/0.50  thf(t78_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.21/0.50              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.21/0.50                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.21/0.50                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.21/0.50                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.21/0.50                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.50         X23 : $i, X24 : $i]:
% 0.21/0.50         (((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.21/0.50          | ((k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20) = (X21))
% 0.21/0.50          | ((X20) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i, 
% 0.21/0.50         X24 : $i]:
% 0.21/0.50         (((k11_mcart_1 @ X19 @ X18 @ X17 @ X16 @ 
% 0.21/0.50            (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)) = (X21))
% 0.21/0.50          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X21) @ 
% 0.21/0.50               (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((X16) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.50              (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               sk_E @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.50              = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '46'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1)
% 0.21/0.50              = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50          = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['48', '54'])).
% 0.21/0.50  thf('56', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50         = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['55', '56', '57', '58', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '60'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.50         X23 : $i, X24 : $i]:
% 0.21/0.50         (((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.21/0.50          | ((k10_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20) = (X24))
% 0.21/0.50          | ((X20) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i, 
% 0.21/0.50         X24 : $i]:
% 0.21/0.50         (((k10_mcart_1 @ X19 @ X18 @ X17 @ X16 @ 
% 0.21/0.50            (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)) = (X24))
% 0.21/0.50          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X21) @ 
% 0.21/0.50               (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((X16) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.50              (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               sk_E @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))
% 0.21/0.50              = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['63', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['47', '60'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1)
% 0.21/0.50              = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50          = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '68'])).
% 0.21/0.50  thf('70', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('71', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('72', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['69', '70', '71', '72', '73'])).
% 0.21/0.50  thf('75', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '74'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, 
% 0.21/0.50         X23 : $i, X24 : $i]:
% 0.21/0.50         (((X16) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.21/0.50          | ((k9_mcart_1 @ X19 @ X18 @ X17 @ X16 @ X20) = (X23))
% 0.21/0.50          | ((X20) != (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X21 : $i, X22 : $i, X23 : $i, 
% 0.21/0.50         X24 : $i]:
% 0.21/0.50         (((k9_mcart_1 @ X19 @ X18 @ X17 @ X16 @ 
% 0.21/0.50            (k4_mcart_1 @ X22 @ X23 @ X24 @ X21)) = (X23))
% 0.21/0.50          | ~ (m1_subset_1 @ (k4_mcart_1 @ X22 @ X23 @ X24 @ X21) @ 
% 0.21/0.50               (k4_zfmisc_1 @ X19 @ X18 @ X17 @ X16))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X17) = (k1_xboole_0))
% 0.21/0.50          | ((X16) = (k1_xboole_0)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['76'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.21/0.50              (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               sk_E @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))
% 0.21/0.50              = (sk_E)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['75', '77'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.21/0.50            (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50            (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['61', '74'])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.21/0.50          | ((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3) = (k1_xboole_0))
% 0.21/0.50          | ((k9_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1) = (sk_E)))),
% 0.21/0.50      inference('demod', [status(thm)], ['78', '79'])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      ((((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '80'])).
% 0.21/0.50  thf('82', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('84', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('85', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('87', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['81', '82', '83', '84', '85', '86'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
