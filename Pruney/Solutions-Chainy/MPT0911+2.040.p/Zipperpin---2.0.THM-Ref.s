%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xjqgvBqUOd

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  132 (1158 expanded)
%              Number of leaves         :   25 ( 363 expanded)
%              Depth                    :   28
%              Number of atoms          : 1823 (26624 expanded)
%              Number of equality atoms :  242 (3770 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t70_mcart_1,axiom,(
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

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_H @ X20 @ X21 @ X19 @ X18 @ X17 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_mcart_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_H @ X20 @ X21 @ X19 @ X18 @ X17 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

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

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['10','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_G @ X20 @ X21 @ X19 @ X18 @ X17 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_mcart_1])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_G @ X20 @ X21 @ X19 @ X18 @ X17 ) @ X18 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

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
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( X20
        = ( k3_mcart_1 @ ( sk_F @ X20 @ X21 @ X19 @ X18 @ X17 ) @ ( sk_G @ X20 @ X21 @ X19 @ X18 @ X17 ) @ ( sk_H @ X20 @ X21 @ X19 @ X18 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[t70_mcart_1])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( X20
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ X20 @ X21 @ X19 @ X18 @ X17 ) @ ( sk_G @ X20 @ X21 @ X19 @ X18 @ X17 ) ) @ ( sk_H @ X20 @ X21 @ X19 @ X18 @ X17 ) ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

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
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X23 @ X22 @ X24 ) )
      | ( sk_D = X24 )
      | ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('46',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ( sk_E
       != ( k4_tarski @ ( k4_tarski @ X23 @ X22 ) @ X24 ) )
      | ( sk_D = X24 )
      | ~ ( m1_subset_1 @ X24 @ sk_C )
      | ~ ( m1_subset_1 @ X23 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_E != sk_E )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('54',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_F @ X20 @ X21 @ X19 @ X18 @ X17 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_mcart_1])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) @ X19 ) )
      | ( X21
        = ( k6_mcart_1 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_F @ X20 @ X21 @ X19 @ X18 @ X17 ) @ X17 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['15','16','17','18'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['52','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['39','40','41','42'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

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

thf('70',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X12 @ X11 @ X10 ) )
      | ( ( k7_mcart_1 @ X12 @ X11 @ X10 @ X13 )
        = X16 )
      | ( X13
       != ( k3_mcart_1 @ X14 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t68_mcart_1])).

thf('71',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_mcart_1 @ X12 @ X11 @ X10 @ ( k3_mcart_1 @ X14 @ X15 @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X14 @ X15 @ X16 ) @ ( k3_zfmisc_1 @ X12 @ X11 @ X10 ) )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('74',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('75',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_mcart_1 @ X12 @ X11 @ X10 @ ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) )
        = X16 )
      | ~ ( m1_subset_1 @ ( k4_tarski @ ( k4_tarski @ X14 @ X15 ) @ X16 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X11 ) @ X10 ) )
      | ( X12 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X3
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X3 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X3 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
        = sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
        = sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['67','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('85',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
     != sk_D )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = sk_D ) ),
    inference(eq_fact,[status(thm)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('87',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('88',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('89',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['90','91','92','93'])).

thf('95',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
     != sk_D )
    | ( ( k2_mcart_1 @ sk_E )
      = sk_D ) ),
    inference(demod,[status(thm)],['85','94'])).

thf('96',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['90','91','92','93'])).

thf('98',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) )
 != sk_D ),
    inference('simplify_reflect-',[status(thm)],['95','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_D )
      | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['83','99'])).

thf('101',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['90','91','92','93'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_D )
      | ( ( k2_mcart_1 @ sk_E )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_D ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xjqgvBqUOd
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 58 iterations in 0.108s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.21/0.57  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.21/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.57  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.57  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.57  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(t71_mcart_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.57       ( ( ![F:$i]:
% 0.21/0.57           ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.57             ( ![G:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.57                 ( ![H:$i]:
% 0.21/0.57                   ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.57                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.57                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.21/0.57         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.57        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.57          ( ( ![F:$i]:
% 0.21/0.57              ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.57                ( ![G:$i]:
% 0.21/0.57                  ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.57                    ( ![H:$i]:
% 0.21/0.57                      ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.57                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.57                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.21/0.57            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.21/0.57  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(d3_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.57       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf(t70_mcart_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.57       ( ( ![F:$i]:
% 0.21/0.57           ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.57             ( ![G:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ G @ B ) =>
% 0.21/0.57                 ( ![H:$i]:
% 0.21/0.57                   ( ( m1_subset_1 @ H @ C ) =>
% 0.21/0.57                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.21/0.57                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.21/0.57         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | (m1_subset_1 @ (sk_H @ X20 @ X21 @ X19 @ X18 @ X17) @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_mcart_1])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.57               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | (m1_subset_1 @ (sk_H @ X20 @ X21 @ X19 @ X18 @ X17) @ X19))),
% 0.21/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.57  thf('7', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('9', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['6', '7', '8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf(t50_mcart_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57          ( ~( ![D:$i]:
% 0.21/0.57               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.57                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.57                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.57                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.57                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.57                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (((X6) = (k1_xboole_0))
% 0.21/0.57          | ((X7) = (k1_xboole_0))
% 0.21/0.57          | ((k6_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.21/0.57              = (k2_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.21/0.57          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.57          | ((X9) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (((X6) = (k1_xboole_0))
% 0.21/0.57          | ((X7) = (k1_xboole_0))
% 0.21/0.57          | ((k6_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.21/0.57              = (k2_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.21/0.57          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.57          | ((X9) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0))
% 0.21/0.57        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.21/0.57            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57        | ((sk_B) = (k1_xboole_0))
% 0.21/0.57        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.57  thf('16', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('17', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('18', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.21/0.57         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('demod', [status(thm)], ['10', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | (m1_subset_1 @ (sk_G @ X20 @ X21 @ X19 @ X18 @ X17) @ X18))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_mcart_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.57               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | (m1_subset_1 @ (sk_G @ X20 @ X21 @ X19 @ X18 @ X17) @ X18))),
% 0.21/0.57      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.57          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.21/0.57         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | ((X20)
% 0.21/0.57              = (k3_mcart_1 @ (sk_F @ X20 @ X21 @ X19 @ X18 @ X17) @ 
% 0.21/0.57                 (sk_G @ X20 @ X21 @ X19 @ X18 @ X17) @ 
% 0.21/0.57                 (sk_H @ X20 @ X21 @ X19 @ X18 @ X17))))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_mcart_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf(d3_mcart_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.57           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.57               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | ((X20)
% 0.21/0.57              = (k4_tarski @ 
% 0.21/0.57                 (k4_tarski @ (sk_F @ X20 @ X21 @ X19 @ X18 @ X17) @ 
% 0.21/0.57                  (sk_G @ X20 @ X21 @ X19 @ X18 @ X17)) @ 
% 0.21/0.57                 (sk_H @ X20 @ X21 @ X19 @ X18 @ X17))))),
% 0.21/0.57      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_E)
% 0.21/0.57            = (k4_tarski @ 
% 0.21/0.57               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.57          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.21/0.57         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_E)
% 0.21/0.57            = (k4_tarski @ 
% 0.21/0.57               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('42', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_E)
% 0.21/0.57            = (k4_tarski @ 
% 0.21/0.57               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.21/0.57          | ((sk_E) != (k3_mcart_1 @ X23 @ X22 @ X24))
% 0.21/0.57          | ((sk_D) = (X24))
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ sk_C)
% 0.21/0.57          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.57           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.21/0.57          | ((sk_E) != (k4_tarski @ (k4_tarski @ X23 @ X22) @ X24))
% 0.21/0.57          | ((sk_D) = (X24))
% 0.21/0.57          | ~ (m1_subset_1 @ X24 @ sk_C)
% 0.21/0.57          | ~ (m1_subset_1 @ X23 @ sk_A))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_E) != (sk_E))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.21/0.57      inference('sup-', [status(thm)], ['43', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.57          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['47'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '48'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.21/0.57          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X17 @ X18 @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | (m1_subset_1 @ (sk_F @ X20 @ X21 @ X19 @ X18 @ X17) @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_mcart_1])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (((X17) = (k1_xboole_0))
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | ((X19) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ 
% 0.21/0.57               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18) @ X19))
% 0.21/0.57          | ((X21) = (k6_mcart_1 @ X17 @ X18 @ X19 @ X20))
% 0.21/0.57          | (m1_subset_1 @ (sk_F @ X20 @ X21 @ X19 @ X18 @ X17) @ X17))),
% 0.21/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((X0) = (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['53', '56'])).
% 0.21/0.57  thf('58', plain,
% 0.21/0.57      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.21/0.57         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['15', '16', '17', '18'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.57      inference('clc', [status(thm)], ['52', '63'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_E)
% 0.21/0.57            = (k4_tarski @ 
% 0.21/0.57               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['39', '40', '41', '42'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((sk_E)
% 0.21/0.57            = (k4_tarski @ 
% 0.21/0.57               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57               sk_D))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['64', '65'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((sk_E)
% 0.21/0.57              = (k4_tarski @ 
% 0.21/0.57                 (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                  (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57                 sk_D)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((sk_E)
% 0.21/0.57              = (k4_tarski @ 
% 0.21/0.57                 (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                  (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57                 sk_D)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['66'])).
% 0.21/0.57  thf(t68_mcart_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57            ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.57              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.57                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.57                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.57                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (((X10) = (k1_xboole_0))
% 0.21/0.57          | ((X11) = (k1_xboole_0))
% 0.21/0.57          | ((X12) = (k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X12 @ X11 @ X10))
% 0.21/0.57          | ((k7_mcart_1 @ X12 @ X11 @ X10 @ X13) = (X16))
% 0.21/0.57          | ((X13) != (k3_mcart_1 @ X14 @ X15 @ X16)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t68_mcart_1])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (((k7_mcart_1 @ X12 @ X11 @ X10 @ (k3_mcart_1 @ X14 @ X15 @ X16))
% 0.21/0.57            = (X16))
% 0.21/0.57          | ~ (m1_subset_1 @ (k3_mcart_1 @ X14 @ X15 @ X16) @ 
% 0.21/0.57               (k3_zfmisc_1 @ X12 @ X11 @ X10))
% 0.21/0.57          | ((X12) = (k1_xboole_0))
% 0.21/0.57          | ((X11) = (k1_xboole_0))
% 0.21/0.57          | ((X10) = (k1_xboole_0)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.57           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.21/0.57           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         (((k7_mcart_1 @ X12 @ X11 @ X10 @ 
% 0.21/0.57            (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16)) = (X16))
% 0.21/0.57          | ~ (m1_subset_1 @ (k4_tarski @ (k4_tarski @ X14 @ X15) @ X16) @ 
% 0.21/0.57               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X11) @ X10))
% 0.21/0.57          | ((X12) = (k1_xboole_0))
% 0.21/0.57          | ((X11) = (k1_xboole_0))
% 0.21/0.57          | ((X10) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.21/0.57          | ((X3) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((X0) = (k1_xboole_0))
% 0.21/0.57          | ((X1) = (k1_xboole_0))
% 0.21/0.57          | ((X2) = (k1_xboole_0))
% 0.21/0.57          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.57              (k4_tarski @ 
% 0.21/0.57               (k4_tarski @ (sk_F @ sk_E @ X3 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57                (sk_G @ sk_E @ X3 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57               sk_D))
% 0.21/0.57              = (sk_D)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['69', '75'])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.57            (k4_tarski @ 
% 0.21/0.57             (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57              (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57             sk_D))
% 0.21/0.57            = (sk_D))
% 0.21/0.57          | ((sk_A) = (k1_xboole_0))
% 0.21/0.57          | ((sk_B) = (k1_xboole_0))
% 0.21/0.57          | ((sk_C) = (k1_xboole_0))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['68', '76'])).
% 0.21/0.57  thf('78', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ 
% 0.21/0.57            (k4_tarski @ 
% 0.21/0.57             (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.57              (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.21/0.57             sk_D))
% 0.21/0.57            = (sk_D))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['77', '78', '79', '80'])).
% 0.21/0.57  thf('82', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['67', '81'])).
% 0.21/0.57  thf('83', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['82'])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.21/0.57          | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['82'])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E)) != (sk_D))
% 0.21/0.57        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D)))),
% 0.21/0.57      inference('eq_fact', [status(thm)], ['84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (((X6) = (k1_xboole_0))
% 0.21/0.57          | ((X7) = (k1_xboole_0))
% 0.21/0.57          | ((k7_mcart_1 @ X6 @ X7 @ X9 @ X8) = (k2_mcart_1 @ X8))
% 0.21/0.57          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.21/0.57          | ((X9) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.57         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.21/0.57           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.57         (((X6) = (k1_xboole_0))
% 0.21/0.57          | ((X7) = (k1_xboole_0))
% 0.21/0.57          | ((k7_mcart_1 @ X6 @ X7 @ X9 @ X8) = (k2_mcart_1 @ X8))
% 0.21/0.57          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.21/0.57          | ((X9) = (k1_xboole_0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      ((((sk_C) = (k1_xboole_0))
% 0.21/0.57        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.21/0.57        | ((sk_B) = (k1_xboole_0))
% 0.21/0.57        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '89'])).
% 0.21/0.57  thf('91', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('92', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('93', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('94', plain,
% 0.21/0.57      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['90', '91', '92', '93'])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      ((((k2_mcart_1 @ (k1_mcart_1 @ sk_E)) != (sk_D))
% 0.21/0.57        | ((k2_mcart_1 @ sk_E) = (sk_D)))),
% 0.21/0.57      inference('demod', [status(thm)], ['85', '94'])).
% 0.21/0.57  thf('96', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['90', '91', '92', '93'])).
% 0.21/0.57  thf('98', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.21/0.57      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('99', plain, (((k2_mcart_1 @ (k1_mcart_1 @ sk_E)) != (sk_D))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['95', '98'])).
% 0.21/0.57  thf('100', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) != (sk_D))
% 0.21/0.57          | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['83', '99'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['90', '91', '92', '93'])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      (![X0 : $i]: (((X0) != (sk_D)) | ((k2_mcart_1 @ sk_E) = (sk_D)))),
% 0.21/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.57  thf('103', plain, (((k2_mcart_1 @ sk_E) = (sk_D))),
% 0.21/0.57      inference('simplify', [status(thm)], ['102'])).
% 0.21/0.57  thf('104', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.21/0.57      inference('demod', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('105', plain, ($false),
% 0.21/0.57      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
