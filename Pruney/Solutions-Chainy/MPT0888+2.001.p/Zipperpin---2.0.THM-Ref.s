%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gWivqdpq4k

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 710 expanded)
%              Number of leaves         :   17 ( 215 expanded)
%              Depth                    :   20
%              Number of atoms          :  919 (16943 expanded)
%              Number of equality atoms :  116 (2150 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i )).

thf(t48_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ~ ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
               => ( D
                  = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2
        = ( k3_mcart_1 @ ( sk_E @ X2 @ X3 @ X1 @ X0 ) @ ( sk_F @ X2 @ X3 @ X1 @ X0 ) @ ( sk_G @ X2 @ X3 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k3_zfmisc_1 @ X0 @ X1 @ X3 ) )
      | ( X3 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l44_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
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
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

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

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X9
       != ( k3_mcart_1 @ X6 @ X7 @ X8 ) )
      | ( ( k7_mcart_1 @ X4 @ X5 @ X10 @ X9 )
        = X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X4 @ X5 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('10',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ ( k3_zfmisc_1 @ X4 @ X5 @ X10 ) )
      | ( ( k7_mcart_1 @ X4 @ X5 @ X10 @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) )
        = X8 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( sk_G @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','18'])).

thf('22',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X9
       != ( k3_mcart_1 @ X6 @ X7 @ X8 ) )
      | ( ( k6_mcart_1 @ X4 @ X5 @ X10 @ X9 )
        = X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X4 @ X5 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('23',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ ( k3_zfmisc_1 @ X4 @ X5 @ X10 ) )
      | ( ( k6_mcart_1 @ X4 @ X5 @ X10 @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) )
        = X7 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
        = ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['6','18'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( sk_F @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ( X9
       != ( k3_mcart_1 @ X6 @ X7 @ X8 ) )
      | ( ( k5_mcart_1 @ X4 @ X5 @ X10 @ X9 )
        = X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k3_zfmisc_1 @ X4 @ X5 @ X10 ) )
      | ( X10 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t47_mcart_1])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ ( k3_zfmisc_1 @ X4 @ X5 @ X10 ) )
      | ( ( k5_mcart_1 @ X4 @ X5 @ X10 @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) )
        = X6 )
      | ( X5 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) )
        = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','31'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D )
        = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( sk_E @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['40','41','42','43'])).

thf('45',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['32','44'])).

thf('46',plain,(
    sk_D
 != ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gWivqdpq4k
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:34:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 30 iterations in 0.022s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.47  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.47  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i).
% 0.21/0.47  thf(t48_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ~( ![D:$i]:
% 0.21/0.47               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.47                 ( ( D ) =
% 0.21/0.47                   ( k3_mcart_1 @
% 0.21/0.47                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.47                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.47                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.47        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47             ( ~( ![D:$i]:
% 0.21/0.47                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.47                    ( ( D ) =
% 0.21/0.47                      ( k3_mcart_1 @
% 0.21/0.47                        ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.47                        ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.47                        ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t48_mcart_1])).
% 0.21/0.47  thf('0', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(l44_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ?[D:$i]:
% 0.21/0.47            ( ( ![E:$i]:
% 0.21/0.47                ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.47                  ( ![F:$i]:
% 0.21/0.47                    ( ( m1_subset_1 @ F @ B ) =>
% 0.21/0.47                      ( ![G:$i]:
% 0.21/0.47                        ( ( m1_subset_1 @ G @ C ) =>
% 0.21/0.47                          ( ( D ) != ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ) ) & 
% 0.21/0.47              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0))
% 0.21/0.47          | ((X1) = (k1_xboole_0))
% 0.21/0.47          | ((X2)
% 0.21/0.47              = (k3_mcart_1 @ (sk_E @ X2 @ X3 @ X1 @ X0) @ 
% 0.21/0.47                 (sk_F @ X2 @ X3 @ X1 @ X0) @ (sk_G @ X2 @ X3 @ X1 @ X0)))
% 0.21/0.47          | ~ (m1_subset_1 @ X2 @ (k3_zfmisc_1 @ X0 @ X1 @ X3))
% 0.21/0.47          | ((X3) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [l44_mcart_1])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((((sk_C) = (k1_xboole_0))
% 0.21/0.47        | ((sk_D)
% 0.21/0.47            = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.47               (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.47               (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.47        | ((sk_B) = (k1_xboole_0))
% 0.21/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.47  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (((sk_D)
% 0.21/0.47         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.47            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.47            (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.47  thf('7', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((sk_D)
% 0.21/0.47         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.47            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.47            (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.47  thf(t47_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ?[D:$i]:
% 0.21/0.47            ( ( ?[E:$i,F:$i,G:$i]:
% 0.21/0.47                ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.21/0.47                       ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.21/0.47                       ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.21/0.47                  ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) & 
% 0.21/0.47              ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.47         (((X4) = (k1_xboole_0))
% 0.21/0.47          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X9) != (k3_mcart_1 @ X6 @ X7 @ X8))
% 0.21/0.48          | ((k7_mcart_1 @ X4 @ X5 @ X10 @ X9) = (X8))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X4 @ X5 @ X10))
% 0.21/0.48          | ((X10) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.48         (((X10) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k3_mcart_1 @ X6 @ X7 @ X8) @ 
% 0.21/0.48               (k3_zfmisc_1 @ X4 @ X5 @ X10))
% 0.21/0.48          | ((k7_mcart_1 @ X4 @ X5 @ X10 @ (k3_mcart_1 @ X6 @ X7 @ X8)) = (X8))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X4) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.48              = (sk_G @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '10'])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_G @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ sk_D)
% 0.21/0.48              = (sk_G @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48            = (sk_G @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['7', '13'])).
% 0.21/0.48  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('16', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48         = (sk_G @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['14', '15', '16', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '18'])).
% 0.21/0.48  thf('20', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '18'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (((X4) = (k1_xboole_0))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X9) != (k3_mcart_1 @ X6 @ X7 @ X8))
% 0.21/0.48          | ((k6_mcart_1 @ X4 @ X5 @ X10 @ X9) = (X7))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X4 @ X5 @ X10))
% 0.21/0.48          | ((X10) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.48         (((X10) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k3_mcart_1 @ X6 @ X7 @ X8) @ 
% 0.21/0.48               (k3_zfmisc_1 @ X4 @ X5 @ X10))
% 0.21/0.48          | ((k6_mcart_1 @ X4 @ X5 @ X10 @ (k3_mcart_1 @ X6 @ X7 @ X8)) = (X7))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X4) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.48              = (sk_F @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['21', '23'])).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (sk_F @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['6', '18'])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k6_mcart_1 @ X2 @ X1 @ X0 @ sk_D)
% 0.21/0.48              = (sk_F @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48            = (sk_F @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['20', '26'])).
% 0.21/0.48  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48         = (sk_F @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['27', '28', '29', '30'])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '31'])).
% 0.21/0.48  thf('33', plain, ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '31'])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.48         (((X4) = (k1_xboole_0))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X9) != (k3_mcart_1 @ X6 @ X7 @ X8))
% 0.21/0.48          | ((k5_mcart_1 @ X4 @ X5 @ X10 @ X9) = (X6))
% 0.21/0.48          | ~ (m1_subset_1 @ X9 @ (k3_zfmisc_1 @ X4 @ X5 @ X10))
% 0.21/0.48          | ((X10) = (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t47_mcart_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.48         (((X10) = (k1_xboole_0))
% 0.21/0.48          | ~ (m1_subset_1 @ (k3_mcart_1 @ X6 @ X7 @ X8) @ 
% 0.21/0.48               (k3_zfmisc_1 @ X4 @ X5 @ X10))
% 0.21/0.48          | ((k5_mcart_1 @ X4 @ X5 @ X10 @ (k3_mcart_1 @ X6 @ X7 @ X8)) = (X6))
% 0.21/0.48          | ((X5) = (k1_xboole_0))
% 0.21/0.48          | ((X4) = (k1_xboole_0)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.21/0.48              (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))
% 0.21/0.48              = (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['34', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (sk_E @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '31'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.48          | ((X2) = (k1_xboole_0))
% 0.21/0.48          | ((X1) = (k1_xboole_0))
% 0.21/0.48          | ((k5_mcart_1 @ X2 @ X1 @ X0 @ sk_D)
% 0.21/0.48              = (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48          | ((X0) = (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain,
% 0.21/0.48      ((((sk_C) = (k1_xboole_0))
% 0.21/0.48        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48            = (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.48        | ((sk_B) = (k1_xboole_0))
% 0.21/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '39'])).
% 0.21/0.48  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('42', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('43', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 0.21/0.48         = (sk_E @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['40', '41', '42', '43'])).
% 0.21/0.48  thf('45', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('demod', [status(thm)], ['32', '44'])).
% 0.21/0.48  thf('46', plain,
% 0.21/0.48      (((sk_D)
% 0.21/0.48         != (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48             (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.21/0.48             (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('47', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
