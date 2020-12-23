%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XEd7DfQaqf

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 274 expanded)
%              Number of leaves         :   23 (  94 expanded)
%              Depth                    :   15
%              Number of atoms          :  976 (6424 expanded)
%              Number of equality atoms :  136 ( 933 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

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

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X11 @ X12 @ X14 @ X13 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) )
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

thf('6',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9
        = ( k3_mcart_1 @ ( sk_E @ X9 @ X10 @ X8 @ X7 ) @ ( sk_F @ X9 @ X10 @ X8 @ X7 ) @ ( sk_G @ X9 @ X10 @ X8 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X7 @ X8 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9
        = ( k4_tarski @ ( k4_tarski @ ( sk_E @ X9 @ X10 @ X8 @ X7 ) @ ( sk_F @ X9 @ X10 @ X8 @ X7 ) ) @ ( sk_G @ X9 @ X10 @ X8 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X7 @ X8 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E_1
      = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['12','13','14','15'])).

thf('18',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X9 @ X10 @ X8 @ X7 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X7 @ X8 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B )
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
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ( sk_D = X22 )
      | ( sk_E_1
       != ( k3_mcart_1 @ X23 @ X22 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ( sk_D = X22 )
      | ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X23 @ X22 ) @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E_1
       != ( k4_tarski @ ( k4_tarski @ X0 @ ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) @ X1 ) )
      | ( sk_D
        = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X9 @ X10 @ X8 @ X7 ) @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X7 @ X8 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_E @ X9 @ X10 @ X8 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X7 @ X8 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('39',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A )
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
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42'])).

thf('44',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( sk_D
      = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','36','43'])).

thf('45',plain,
    ( sk_D
    = ( sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','45'])).

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

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X17 @ X16 @ X15 ) )
      | ( ( k6_mcart_1 @ X17 @ X16 @ X15 @ X18 )
        = X20 )
      | ( X18
       != ( k3_mcart_1 @ X19 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t68_mcart_1])).

thf('48',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k6_mcart_1 @ X17 @ X16 @ X15 @ ( k3_mcart_1 @ X19 @ X20 @ X21 ) )
        = X20 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X19 @ X20 @ X21 ) @ ( k3_zfmisc_1 @ X17 @ X16 @ X15 ) )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('51',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i,X20: $i,X21: $i] :
      ( ( ( k6_mcart_1 @ X17 @ X16 @ X15 @ ( k4_tarski @ ( k4_tarski @ X19 @ X20 ) @ X21 ) )
        = X20 )
      | ~ ( m1_subset_1 @ ( k4_tarski @ ( k4_tarski @ X19 @ X20 ) @ X21 ) @ ( k3_zfmisc_1 @ X17 @ X16 @ X15 ) )
      | ( X17 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,
    ( sk_E_1
    = ( k4_tarski @ ( k4_tarski @ ( sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A ) @ sk_D ) @ ( sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','45'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_E_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1 )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
      = sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','54'])).

thf('56',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = sk_D ),
    inference('simplify_reflect-',[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) )
    = sk_D ),
    inference('sup+',[status(thm)],['6','59'])).

thf('61',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('63',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XEd7DfQaqf
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 33 iterations in 0.023s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.21/0.48  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.48  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.48  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
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
% 0.21/0.48  thf(t50_mcart_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ~( ![D:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.48                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.48                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.48                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.48                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.48                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.48         (((X11) = (k1_xboole_0))
% 0.21/0.48          | ((X12) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X11 @ X12 @ X14 @ X13)
% 0.21/0.48              = (k2_mcart_1 @ (k1_mcart_1 @ X13)))
% 0.21/0.48          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X11 @ X12 @ X14))
% 0.21/0.48          | ((X14) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.21/0.48            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))
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
% 0.21/0.48      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.21/0.48         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain,
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
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((X7) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | ((X9)
% 0.21/0.49              = (k3_mcart_1 @ (sk_E @ X9 @ X10 @ X8 @ X7) @ 
% 0.21/0.49                 (sk_F @ X9 @ X10 @ X8 @ X7) @ (sk_G @ X9 @ X10 @ X8 @ X7)))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X7 @ X8 @ X10))
% 0.21/0.49          | ((X10) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf(d3_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((X7) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | ((X9)
% 0.21/0.49              = (k4_tarski @ 
% 0.21/0.49                 (k4_tarski @ (sk_E @ X9 @ X10 @ X8 @ X7) @ 
% 0.21/0.49                  (sk_F @ X9 @ X10 @ X8 @ X7)) @ 
% 0.21/0.49                 (sk_G @ X9 @ X10 @ X8 @ X7)))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X7 @ X8 @ X10))
% 0.21/0.49          | ((X10) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | ((sk_E_1)
% 0.21/0.49            = (k4_tarski @ 
% 0.21/0.49               (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49                (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.49               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '11'])).
% 0.21/0.49  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('14', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k4_tarski @ 
% 0.21/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k4_tarski @ 
% 0.21/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.49             (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['12', '13', '14', '15'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((X7) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_F @ X9 @ X10 @ X8 @ X7) @ X8)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X7 @ X8 @ X10))
% 0.21/0.49          | ((X10) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('20', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.49  thf('21', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('22', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('23', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['20', '21', '22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.21/0.49          | ((sk_D) = (X22))
% 0.21/0.49          | ((sk_E_1) != (k3_mcart_1 @ X23 @ X22 @ X24))
% 0.21/0.49          | ~ (m1_subset_1 @ X24 @ sk_C)
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.21/0.49          | ((sk_D) = (X22))
% 0.21/0.49          | ((sk_E_1) != (k4_tarski @ (k4_tarski @ X23 @ X22) @ X24))
% 0.21/0.49          | ~ (m1_subset_1 @ X24 @ sk_C)
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.49          | ((sk_E_1)
% 0.21/0.49              != (k4_tarski @ 
% 0.21/0.49                  (k4_tarski @ X0 @ (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)) @ X1))
% 0.21/0.49          | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      ((((sk_E_1) != (sk_E_1))
% 0.21/0.49        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.49        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['17', '28'])).
% 0.21/0.49  thf('30', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((X7) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_G @ X9 @ X10 @ X8 @ X7) @ X10)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X7 @ X8 @ X10))
% 0.21/0.49          | ((X10) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.49  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('34', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['32', '33', '34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.49         (((X7) = (k1_xboole_0))
% 0.21/0.49          | ((X8) = (k1_xboole_0))
% 0.21/0.49          | (m1_subset_1 @ (sk_E @ X9 @ X10 @ X8 @ X7) @ X7)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X7 @ X8 @ X10))
% 0.21/0.49          | ((X10) = (k1_xboole_0)))),
% 0.21/0.49      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      ((((sk_C) = (k1_xboole_0))
% 0.21/0.49        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      ((((sk_E_1) != (sk_E_1))
% 0.21/0.49        | ((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '36', '43'])).
% 0.21/0.49  thf('45', plain, (((sk_D) = (sk_F @ sk_E_1 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.49      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k4_tarski @ 
% 0.21/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D) @ 
% 0.21/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '45'])).
% 0.21/0.49  thf(t68_mcart_1, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.49       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.49            ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.49              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.49                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.49                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.49                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         (((X15) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((X17) = (k1_xboole_0))
% 0.21/0.49          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X17 @ X16 @ X15))
% 0.21/0.49          | ((k6_mcart_1 @ X17 @ X16 @ X15 @ X18) = (X20))
% 0.21/0.49          | ((X18) != (k3_mcart_1 @ X19 @ X20 @ X21)))),
% 0.21/0.49      inference('cnf', [status(esa)], [t68_mcart_1])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         (((k6_mcart_1 @ X17 @ X16 @ X15 @ (k3_mcart_1 @ X19 @ X20 @ X21))
% 0.21/0.49            = (X20))
% 0.21/0.49          | ~ (m1_subset_1 @ (k3_mcart_1 @ X19 @ X20 @ X21) @ 
% 0.21/0.49               (k3_zfmisc_1 @ X17 @ X16 @ X15))
% 0.21/0.49          | ((X17) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.49           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.49      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.49         (((k6_mcart_1 @ X17 @ X16 @ X15 @ 
% 0.21/0.49            (k4_tarski @ (k4_tarski @ X19 @ X20) @ X21)) = (X20))
% 0.21/0.49          | ~ (m1_subset_1 @ (k4_tarski @ (k4_tarski @ X19 @ X20) @ X21) @ 
% 0.21/0.49               (k3_zfmisc_1 @ X17 @ X16 @ X15))
% 0.21/0.49          | ((X17) = (k1_xboole_0))
% 0.21/0.49          | ((X16) = (k1_xboole_0))
% 0.21/0.49          | ((X15) = (k1_xboole_0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.49              (k4_tarski @ 
% 0.21/0.49               (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D) @ 
% 0.21/0.49               (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.49              = (sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (((sk_E_1)
% 0.21/0.49         = (k4_tarski @ 
% 0.21/0.49            (k4_tarski @ (sk_E @ sk_E_1 @ sk_C @ sk_B @ sk_A) @ sk_D) @ 
% 0.21/0.49            (sk_G @ sk_E_1 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '45'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ sk_E_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.49          | ((X0) = (k1_xboole_0))
% 0.21/0.49          | ((X1) = (k1_xboole_0))
% 0.21/0.49          | ((X2) = (k1_xboole_0))
% 0.21/0.49          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ sk_E_1) = (sk_D)))),
% 0.21/0.49      inference('demod', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      ((((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))
% 0.21/0.49        | ((sk_A) = (k1_xboole_0))
% 0.21/0.49        | ((sk_B) = (k1_xboole_0))
% 0.21/0.49        | ((sk_C) = (k1_xboole_0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['7', '54'])).
% 0.21/0.49  thf('56', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain, (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1) = (sk_D))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.49  thf('60', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)) = (sk_D))),
% 0.21/0.49      inference('sup+', [status(thm)], ['6', '59'])).
% 0.21/0.49  thf('61', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E_1)
% 0.21/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.49  thf('63', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain, ($false),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['60', '63'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
