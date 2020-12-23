%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4oosjMzVNB

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:15 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 287 expanded)
%              Number of leaves         :   21 (  99 expanded)
%              Depth                    :   13
%              Number of atoms          :  982 (8728 expanded)
%              Number of equality atoms :  134 (1228 expanded)
%              Maximal formula depth    :   27 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(t82_mcart_1,conjecture,(
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
                         => ( E = J ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

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
                           => ( E = J ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_mcart_1])).

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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17
        = ( k4_mcart_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ sk_B )
      | ~ ( m1_subset_1 @ X29 @ sk_D )
      | ( sk_E = X29 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X30 @ X28 @ X31 @ X29 ) )
      | ~ ( m1_subset_1 @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ( sk_E = X2 )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
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
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','28','36','44'])).

thf('46',plain,
    ( sk_E
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
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

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X23 @ ( k4_zfmisc_1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( ( k11_mcart_1 @ X22 @ X21 @ X20 @ X19 @ X23 )
        = X24 )
      | ( X23
       != ( k4_mcart_1 @ X25 @ X26 @ X27 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( ( k11_mcart_1 @ X22 @ X21 @ X20 @ X19 @ ( k4_mcart_1 @ X25 @ X26 @ X27 @ X24 ) )
        = X24 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X25 @ X26 @ X27 @ X24 ) @ ( k4_zfmisc_1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( X22 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['8','46'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1 )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54','55','56','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4oosjMzVNB
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:44:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 50 iterations in 0.038s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.49  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(t82_mcart_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.19/0.49       ( ( ![G:$i]:
% 0.19/0.49           ( ( m1_subset_1 @ G @ A ) =>
% 0.19/0.49             ( ![H:$i]:
% 0.19/0.49               ( ( m1_subset_1 @ H @ B ) =>
% 0.19/0.49                 ( ![I:$i]:
% 0.19/0.49                   ( ( m1_subset_1 @ I @ C ) =>
% 0.19/0.49                     ( ![J:$i]:
% 0.19/0.49                       ( ( m1_subset_1 @ J @ D ) =>
% 0.19/0.49                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.19/0.49                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.19/0.49         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.19/0.49          ( ( ![G:$i]:
% 0.19/0.49              ( ( m1_subset_1 @ G @ A ) =>
% 0.19/0.49                ( ![H:$i]:
% 0.19/0.49                  ( ( m1_subset_1 @ H @ B ) =>
% 0.19/0.49                    ( ![I:$i]:
% 0.19/0.49                      ( ( m1_subset_1 @ I @ C ) =>
% 0.19/0.49                        ( ![J:$i]:
% 0.19/0.49                          ( ( m1_subset_1 @ J @ D ) =>
% 0.19/0.49                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.19/0.49                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.19/0.49            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.19/0.49              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(l68_mcart_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49          ( ?[E:$i]:
% 0.19/0.49            ( ( ![F:$i]:
% 0.19/0.49                ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.49                  ( ![G:$i]:
% 0.19/0.49                    ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.49                      ( ![H:$i]:
% 0.19/0.49                        ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.49                          ( ![I:$i]:
% 0.19/0.49                            ( ( m1_subset_1 @ I @ D ) =>
% 0.19/0.49                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.19/0.49              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (((X14) = (k1_xboole_0))
% 0.19/0.49          | ((X15) = (k1_xboole_0))
% 0.19/0.49          | ((X16) = (k1_xboole_0))
% 0.19/0.49          | ((X17)
% 0.19/0.49              = (k4_mcart_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.19/0.49                 (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.19/0.49                 (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.19/0.49                 (sk_I @ X17 @ X18 @ X16 @ X15 @ X14)))
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      ((((sk_D) = (k1_xboole_0))
% 0.19/0.49        | ((sk_F_1)
% 0.19/0.49            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf('4', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('5', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (((sk_F_1)
% 0.19/0.49         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (((sk_F_1)
% 0.19/0.49         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['3', '4', '5', '6', '7'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (((X14) = (k1_xboole_0))
% 0.19/0.49          | ((X15) = (k1_xboole_0))
% 0.19/0.49          | ((X16) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ X15)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      ((((sk_D) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('16', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)],
% 0.19/0.49                ['12', '13', '14', '15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X28 @ sk_B)
% 0.19/0.49          | ~ (m1_subset_1 @ X29 @ sk_D)
% 0.19/0.49          | ((sk_E) = (X29))
% 0.19/0.49          | ((sk_F_1) != (k4_mcart_1 @ X30 @ X28 @ X31 @ X29))
% 0.19/0.49          | ~ (m1_subset_1 @ X31 @ sk_C)
% 0.19/0.49          | ~ (m1_subset_1 @ X30 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.19/0.49          | ((sk_F_1)
% 0.19/0.49              != (k4_mcart_1 @ X0 @ 
% 0.19/0.49                  (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.19/0.49          | ((sk_E) = (X2))
% 0.19/0.49          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((((sk_F_1) != (sk_F_1))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.19/0.49        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['9', '19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (((X14) = (k1_xboole_0))
% 0.19/0.49          | ((X15) = (k1_xboole_0))
% 0.19/0.49          | ((X16) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_I @ X17 @ X18 @ X16 @ X15 @ X14) @ X18)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      ((((sk_D) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('26', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('27', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)],
% 0.19/0.49                ['23', '24', '25', '26', '27'])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (((X14) = (k1_xboole_0))
% 0.19/0.49          | ((X15) = (k1_xboole_0))
% 0.19/0.49          | ((X16) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ X16)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((((sk_D) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.49  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('35', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)],
% 0.19/0.49                ['31', '32', '33', '34', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (((X14) = (k1_xboole_0))
% 0.19/0.49          | ((X15) = (k1_xboole_0))
% 0.19/0.49          | ((X16) = (k1_xboole_0))
% 0.19/0.49          | (m1_subset_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ X14)
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.19/0.49          | ((X18) = (k1_xboole_0)))),
% 0.19/0.49      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      ((((sk_D) = (k1_xboole_0))
% 0.19/0.49        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.49  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('43', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)],
% 0.19/0.49                ['39', '40', '41', '42', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      ((((sk_F_1) != (sk_F_1))
% 0.19/0.49        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['20', '28', '36', '44'])).
% 0.19/0.49  thf('46', plain, (((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.19/0.49      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      (((sk_F_1)
% 0.19/0.49         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '46'])).
% 0.19/0.49  thf(t78_mcart_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.19/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.19/0.49            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.19/0.49              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.19/0.49                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.19/0.49                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.19/0.49                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.19/0.49                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.19/0.49         X26 : $i, X27 : $i]:
% 0.19/0.49         (((X19) = (k1_xboole_0))
% 0.19/0.49          | ((X20) = (k1_xboole_0))
% 0.19/0.49          | ((X21) = (k1_xboole_0))
% 0.19/0.49          | ((X22) = (k1_xboole_0))
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (k4_zfmisc_1 @ X22 @ X21 @ X20 @ X19))
% 0.19/0.49          | ((k11_mcart_1 @ X22 @ X21 @ X20 @ X19 @ X23) = (X24))
% 0.19/0.49          | ((X23) != (k4_mcart_1 @ X25 @ X26 @ X27 @ X24)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X24 : $i, X25 : $i, X26 : $i, 
% 0.19/0.49         X27 : $i]:
% 0.19/0.49         (((k11_mcart_1 @ X22 @ X21 @ X20 @ X19 @ 
% 0.19/0.49            (k4_mcart_1 @ X25 @ X26 @ X27 @ X24)) = (X24))
% 0.19/0.49          | ~ (m1_subset_1 @ (k4_mcart_1 @ X25 @ X26 @ X27 @ X24) @ 
% 0.19/0.49               (k4_zfmisc_1 @ X22 @ X21 @ X20 @ X19))
% 0.19/0.49          | ((X22) = (k1_xboole_0))
% 0.19/0.49          | ((X21) = (k1_xboole_0))
% 0.19/0.49          | ((X20) = (k1_xboole_0))
% 0.19/0.49          | ((X19) = (k1_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.49          | ((X0) = (k1_xboole_0))
% 0.19/0.49          | ((X1) = (k1_xboole_0))
% 0.19/0.49          | ((X2) = (k1_xboole_0))
% 0.19/0.49          | ((X3) = (k1_xboole_0))
% 0.19/0.49          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.19/0.49              (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.19/0.49              = (sk_E)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['47', '49'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((sk_F_1)
% 0.19/0.49         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.49            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.19/0.49      inference('demod', [status(thm)], ['8', '46'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.19/0.49          | ((X0) = (k1_xboole_0))
% 0.19/0.49          | ((X1) = (k1_xboole_0))
% 0.19/0.49          | ((X2) = (k1_xboole_0))
% 0.19/0.49          | ((X3) = (k1_xboole_0))
% 0.19/0.49          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ sk_F_1) = (sk_E)))),
% 0.19/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      ((((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.19/0.49        | ((sk_A) = (k1_xboole_0))
% 0.19/0.49        | ((sk_B) = (k1_xboole_0))
% 0.19/0.49        | ((sk_C) = (k1_xboole_0))
% 0.19/0.49        | ((sk_D) = (k1_xboole_0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '52'])).
% 0.19/0.49  thf('54', plain, (((sk_D) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('55', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('56', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('57', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('59', plain, ($false),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)],
% 0.19/0.49                ['53', '54', '55', '56', '57', '58'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
