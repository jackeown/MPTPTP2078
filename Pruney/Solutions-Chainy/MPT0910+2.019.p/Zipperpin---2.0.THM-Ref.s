%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N6DlIhb9cq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 475 expanded)
%              Number of leaves         :   21 ( 151 expanded)
%              Depth                    :   14
%              Number of atoms          :  911 (11688 expanded)
%              Number of equality atoms :  127 (1716 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_G_1_type,type,(
    sk_G_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F_1 @ X10 @ X11 @ X9 @ X8 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10
        = ( k3_mcart_1 @ ( sk_E @ X10 @ X11 @ X9 @ X8 ) @ ( sk_F_1 @ X10 @ X11 @ X9 @ X8 ) @ ( sk_G_1 @ X10 @ X11 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ sk_B )
      | ( sk_D = X18 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X19 @ X18 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ sk_C )
      | ~ ( m1_subset_1 @ X19 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k3_mcart_1 @ X0 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ X1 ) )
      | ( sk_D
        = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G_1 @ X10 @ X11 @ X9 @ X8 ) @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X10 @ X11 @ X9 @ X8 ) @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','24','31'])).

thf('33',plain,
    ( sk_D
    = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ sk_B ),
    inference(demod,[status(thm)],['6','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ X1 )
      | ( X4
        = ( k3_mcart_1 @ ( sk_F @ X2 @ X4 ) @ ( sk_G @ X2 @ X4 ) @ ( sk_H @ X2 @ X4 ) ) )
      | ( X2
        = ( k6_mcart_1 @ X0 @ X1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d6_mcart_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) )
      | ( sk_E_1
        = ( k3_mcart_1 @ ( sk_F @ X0 @ sk_E_1 ) @ ( sk_G @ X0 @ sk_E_1 ) @ ( sk_H @ X0 @ sk_E_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) )
      | ( sk_E_1
        = ( k3_mcart_1 @ ( sk_F @ X0 @ sk_E_1 ) @ ( sk_G @ X0 @ sk_E_1 ) @ ( sk_H @ X0 @ sk_E_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( sk_E_1
      = ( k3_mcart_1 @ ( sk_F @ sk_D @ sk_E_1 ) @ ( sk_G @ sk_D @ sk_E_1 ) @ ( sk_H @ sk_D @ sk_E_1 ) ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_F @ sk_D @ sk_E_1 ) @ ( sk_G @ sk_D @ sk_E_1 ) @ ( sk_H @ sk_D @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf(t28_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( k3_mcart_1 @ A @ B @ C )
        = ( k3_mcart_1 @ D @ E @ F ) )
     => ( ( A = D )
        & ( B = E )
        & ( C = F ) ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X16 = X14 )
      | ( ( k3_mcart_1 @ X13 @ X16 @ X17 )
       != ( k3_mcart_1 @ X12 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t28_mcart_1])).

thf('46',plain,(
    ! [X13: $i,X16: $i,X17: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X13 @ X16 @ X17 ) )
      = X16 ) ),
    inference(inj_rec,[status(thm)],['45'])).

thf('47',plain,
    ( ( '#_fresh_sk2' @ sk_E_1 )
    = ( sk_G @ sk_D @ sk_E_1 ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('49',plain,
    ( sk_D
    = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('50',plain,
    ( sk_E_1
    = ( k3_mcart_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D @ ( sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X13: $i,X16: $i,X17: $i] :
      ( ( '#_fresh_sk2' @ ( k3_mcart_1 @ X13 @ X16 @ X17 ) )
      = X16 ) ),
    inference(inj_rec,[status(thm)],['45'])).

thf('52',plain,
    ( ( '#_fresh_sk2' @ sk_E_1 )
    = sk_D ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,
    ( sk_D
    = ( sk_G @ sk_D @ sk_E_1 ) ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    m1_subset_1 @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('55',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X2 @ X1 )
      | ( X2
       != ( sk_G @ X2 @ X4 ) )
      | ( X2
        = ( k6_mcart_1 @ X0 @ X1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d6_mcart_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) )
      | ( X0
       != ( sk_G @ X0 @ sk_E_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) )
      | ( X0
       != ( sk_G @ X0 @ sk_E_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A )
     != ( sk_G @ ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_E_1 ) )
    | ( ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A )
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['54','61'])).

thf('63',plain,
    ( sk_D
    = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('64',plain,
    ( sk_D
    = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('65',plain,
    ( sk_D
    = ( sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('66',plain,
    ( ( sk_D
     != ( sk_G @ sk_D @ sk_E_1 ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_D
 != ( sk_G @ sk_D @ sk_E_1 ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.N6DlIhb9cq
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 56 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i > $i > $i).
% 0.21/0.48  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_H_type, type, sk_H: $i > $i > $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_G_type, type, sk_G: $i > $i > $i).
% 0.21/0.48  thf('#_fresh_sk2_type', type, '#_fresh_sk2': $i > $i).
% 0.21/0.48  thf(sk_G_1_type, type, sk_G_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(t70_mcart_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48       ( ( ![F:$i]:
% 0.21/0.48           ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.48             ( ![G:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.48                 ( ![H:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.48                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.48                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.21/0.48         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.48        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48          ( ( ![F:$i]:
% 0.21/0.48              ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.48                ( ![G:$i]:
% 0.21/0.48                  ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.48                    ( ![H:$i]:
% 0.21/0.48                      ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.48                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.48                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.21/0.48            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.48              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(l44_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ?[D:$i]:
% 0.21/0.48            ( ( ![E:$i]:
% 0.21/0.48                ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.48                  ( ![F:$i]:
% 0.21/0.48                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.48                      ( ![G:$i]:
% 0.21/0.48                        ( ( m1_subset_1 @ G @ C ) =>
% 0.21/0.48                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.21/0.48              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_F_1 @ X10 @ X11 @ X9 @ X8) @ X9)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (k3_zfmisc_1 @ X8 @ X9 @ X11))
% 0.21/0.48          | ((X11) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | (m1_subset_1 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.48  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | ((X10)
% 0.21/0.48              = (k3_mcart_1 @ (sk_E @ X10 @ X11 @ X9 @ X8) @ 
% 0.21/0.48                 (sk_F_1 @ X10 @ X11 @ X9 @ X8) @ 
% 0.21/0.48                 (sk_G_1 @ X10 @ X11 @ X9 @ X8)))
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (k3_zfmisc_1 @ X8 @ X9 @ X11))
% 0.21/0.48          | ((X11) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((sk_E_1)
% 0.21/0.48            = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.48  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('12', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X18 @ sk_B)
% 0.21/0.48          | ((sk_D) = (X18))
% 0.21/0.48          | ((sk_E_1) != (k3_mcart_1 @ X19 @ X18 @ X20))
% 0.21/0.48          | ~ (m1_subset_1 @ X20 @ sk_C)
% 0.21/0.48          | ~ (m1_subset_1 @ X19 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.48          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.48          | ((sk_E_1)
% 0.21/0.48              != (k3_mcart_1 @ X0 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ X1))
% 0.21/0.48          | ((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      ((((sk_E_1) != (sk_E_1))
% 0.21/0.48        | ((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ~ (m1_subset_1 @ (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.48        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_G_1 @ X10 @ X11 @ X9 @ X8) @ X11)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (k3_zfmisc_1 @ X8 @ X9 @ X11))
% 0.21/0.48          | ((X11) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | (m1_subset_1 @ (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.48         (((X8) = (k1_xboole_0))
% 0.21/0.48          | ((X9) = (k1_xboole_0))
% 0.21/0.48          | (m1_subset_1 @ (sk_E @ X10 @ X11 @ X9 @ X8) @ X8)
% 0.21/0.48          | ~ (m1_subset_1 @ X10 @ (k3_zfmisc_1 @ X8 @ X9 @ X11))
% 0.21/0.48          | ((X11) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.48  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      ((((sk_E_1) != (sk_E_1))
% 0.21/0.48        | ((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '24', '31'])).
% 0.21/0.48  thf('33', plain, (((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('34', plain, ((m1_subset_1 @ sk_D @ sk_B)),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '33'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d6_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ~( ![D:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48                 ( ![E:$i]:
% 0.21/0.48                   ( ( m1_subset_1 @ E @ B ) =>
% 0.21/0.48                     ( ( ( E ) = ( k6_mcart_1 @ A @ B @ C @ D ) ) <=>
% 0.21/0.48                       ( ![F:$i,G:$i,H:$i]:
% 0.21/0.48                         ( ( ( D ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.48                           ( ( E ) = ( G ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ X1)
% 0.21/0.48          | ((X4)
% 0.21/0.48              = (k3_mcart_1 @ (sk_F @ X2 @ X4) @ (sk_G @ X2 @ X4) @ 
% 0.21/0.48                 (sk_H @ X2 @ X4)))
% 0.21/0.48          | ((X2) = (k6_mcart_1 @ X0 @ X1 @ X3 @ X4))
% 0.21/0.48          | ~ (m1_subset_1 @ X4 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.21/0.48          | ((X3) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d6_mcart_1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_C) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))
% 0.21/0.48          | ((sk_E_1)
% 0.21/0.48              = (k3_mcart_1 @ (sk_F @ X0 @ sk_E_1) @ (sk_G @ X0 @ sk_E_1) @ 
% 0.21/0.48                 (sk_H @ X0 @ sk_E_1)))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | ((sk_B) = (k1_xboole_0))
% 0.21/0.48          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))
% 0.21/0.48          | ((sk_E_1)
% 0.21/0.48              = (k3_mcart_1 @ (sk_F @ X0 @ sk_E_1) @ (sk_G @ X0 @ sk_E_1) @ 
% 0.21/0.48                 (sk_H @ X0 @ sk_E_1)))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      ((((sk_E_1)
% 0.21/0.48          = (k3_mcart_1 @ (sk_F @ sk_D @ sk_E_1) @ (sk_G @ sk_D @ sk_E_1) @ 
% 0.21/0.48             (sk_H @ sk_D @ sk_E_1)))
% 0.21/0.48        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '41'])).
% 0.21/0.48  thf('43', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_F @ sk_D @ sk_E_1) @ (sk_G @ sk_D @ sk_E_1) @ 
% 0.21/0.48            (sk_H @ sk_D @ sk_E_1)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.48  thf(t28_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.48     ( ( ( k3_mcart_1 @ A @ B @ C ) = ( k3_mcart_1 @ D @ E @ F ) ) =>
% 0.21/0.48       ( ( ( A ) = ( D ) ) & ( ( B ) = ( E ) ) & ( ( C ) = ( F ) ) ) ))).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         (((X16) = (X14))
% 0.21/0.48          | ((k3_mcart_1 @ X13 @ X16 @ X17) != (k3_mcart_1 @ X12 @ X14 @ X15)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t28_mcart_1])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (![X13 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         (('#_fresh_sk2' @ (k3_mcart_1 @ X13 @ X16 @ X17)) = (X16))),
% 0.21/0.48      inference('inj_rec', [status(thm)], ['45'])).
% 0.21/0.48  thf('47', plain, ((('#_fresh_sk2' @ sk_E_1) = (sk_G @ sk_D @ sk_E_1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['44', '46'])).
% 0.21/0.48  thf('48', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 0.21/0.48  thf('49', plain, (((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('50', plain,
% 0.21/0.48      (((sk_E_1)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D @ 
% 0.21/0.48            (sk_G_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.48  thf('51', plain,
% 0.21/0.48      (![X13 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         (('#_fresh_sk2' @ (k3_mcart_1 @ X13 @ X16 @ X17)) = (X16))),
% 0.21/0.48      inference('inj_rec', [status(thm)], ['45'])).
% 0.21/0.48  thf('52', plain, ((('#_fresh_sk2' @ sk_E_1) = (sk_D))),
% 0.21/0.48      inference('sup+', [status(thm)], ['50', '51'])).
% 0.21/0.48  thf('53', plain, (((sk_D) = (sk_G @ sk_D @ sk_E_1))),
% 0.21/0.48      inference('demod', [status(thm)], ['47', '52'])).
% 0.21/0.48  thf('54', plain,
% 0.21/0.48      ((m1_subset_1 @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.48  thf('55', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('56', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (((X0) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ X2 @ X1)
% 0.21/0.48          | ((X2) != (sk_G @ X2 @ X4))
% 0.21/0.48          | ((X2) = (k6_mcart_1 @ X0 @ X1 @ X3 @ X4))
% 0.21/0.48          | ~ (m1_subset_1 @ X4 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.21/0.48          | ((X3) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d6_mcart_1])).
% 0.21/0.48  thf('57', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_C) = (k1_xboole_0))
% 0.21/0.48          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))
% 0.21/0.48          | ((X0) != (sk_G @ X0 @ sk_E_1))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.21/0.48          | ((sk_B) = (k1_xboole_0))
% 0.21/0.48          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.48  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('59', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('60', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('61', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))
% 0.21/0.48          | ((X0) != (sk_G @ X0 @ sk_E_1))
% 0.21/0.48          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['57', '58', '59', '60'])).
% 0.21/0.48  thf('62', plain,
% 0.21/0.48      ((((sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48          != (sk_G @ (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_E_1))
% 0.21/0.48        | ((sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A)
% 0.21/0.48            = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['54', '61'])).
% 0.21/0.48  thf('63', plain, (((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('64', plain, (((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('65', plain, (((sk_D) = (sk_F_1 @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.48  thf('66', plain,
% 0.21/0.48      ((((sk_D) != (sk_G @ sk_D @ sk_E_1))
% 0.21/0.48        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)))),
% 0.21/0.48      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.21/0.48  thf('67', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('68', plain, (((sk_D) != (sk_G @ sk_D @ sk_E_1))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.21/0.48  thf('69', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['53', '68'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
