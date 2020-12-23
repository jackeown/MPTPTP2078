%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZZ9alnzCZE

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 253 expanded)
%              Number of leaves         :   26 (  91 expanded)
%              Depth                    :   12
%              Number of atoms          : 1298 (7365 expanded)
%              Number of equality atoms :  186 (1054 expanded)
%              Maximal formula depth    :   26 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf('#_fresh_sk4_type',type,(
    '#_fresh_sk4': $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X17
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k9_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k10_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17 ) @ ( k11_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('4',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X18 @ X19 @ X20 @ X22 @ X21 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('5',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X18 @ X19 @ X20 @ X22 @ X21 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('13',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X18 @ X19 @ X20 @ X22 @ X21 )
        = ( k2_mcart_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k4_zfmisc_1 @ X18 @ X19 @ X20 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('21',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ sk_F_1 ) )
    | ( sk_C = k1_xboole_0 )
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
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('27',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','10','18','26'])).

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
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['27','28','29','30','31'])).

thf(t33_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( k4_mcart_1 @ A @ B @ C @ D )
        = ( k4_mcart_1 @ E @ F @ G @ H ) )
     => ( ( A = E )
        & ( B = F )
        & ( C = G )
        & ( D = H ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X12 = X9 )
      | ( ( k4_mcart_1 @ X6 @ X10 @ X11 @ X12 )
       != ( k4_mcart_1 @ X5 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t33_mcart_1])).

thf('34',plain,(
    ! [X6: $i,X10: $i,X11: $i,X12: $i] :
      ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ X6 @ X10 @ X11 @ X12 ) )
      = X12 ) ),
    inference(inj_rec,[status(thm)],['33'])).

thf('35',plain,
    ( ( '#_fresh_sk4' @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3
        = ( k4_mcart_1 @ ( sk_F @ X3 @ X4 @ X2 @ X1 @ X0 ) @ ( sk_G @ X3 @ X4 @ X2 @ X1 @ X0 ) @ ( sk_H @ X3 @ X4 @ X2 @ X1 @ X0 ) @ ( sk_I @ X3 @ X4 @ X2 @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('38',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['38','39','40','41','42'])).

thf('45',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X3 @ X4 @ X2 @ X1 @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ sk_B )
      | ~ ( m1_subset_1 @ X24 @ sk_D )
      | ( sk_E = X24 )
      | ( sk_F_1
       != ( k4_mcart_1 @ X25 @ X23 @ X26 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ sk_C )
      | ~ ( m1_subset_1 @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X1 @ X2 ) )
      | ( sk_E = X2 )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X3 @ X4 @ X2 @ X1 @ X0 ) @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('58',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X3 @ X4 @ X2 @ X1 @ X0 ) @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('66',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X3 @ X4 @ X2 @ X1 @ X0 ) @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4 ) )
      | ( X4 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('74',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','63','71','79'])).

thf('81',plain,
    ( sk_E
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ),
    inference(demod,[status(thm)],['43','81'])).

thf('83',plain,(
    ! [X6: $i,X10: $i,X11: $i,X12: $i] :
      ( ( '#_fresh_sk4' @ ( k4_mcart_1 @ X6 @ X10 @ X11 @ X12 ) )
      = X12 ) ),
    inference(inj_rec,[status(thm)],['33'])).

thf('84',plain,
    ( ( '#_fresh_sk4' @ sk_F_1 )
    = sk_E ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( sk_E
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference(demod,[status(thm)],['35','84'])).

thf('86',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
    = ( k2_mcart_1 @ sk_F_1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('88',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F_1 ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['85','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZZ9alnzCZE
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:52:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 64 iterations in 0.038s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf('#_fresh_sk4_type', type, '#_fresh_sk4': $i > $i).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.21/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(t82_mcart_1, conjecture,
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
% 0.21/0.50                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
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
% 0.21/0.50                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.21/0.50            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.21/0.50              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t60_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ~( ![E:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50                 ( ( E ) =
% 0.21/0.50                   ( k4_mcart_1 @
% 0.21/0.50                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.21/0.50                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.50         (((X13) = (k1_xboole_0))
% 0.21/0.50          | ((X14) = (k1_xboole_0))
% 0.21/0.50          | ((X15) = (k1_xboole_0))
% 0.21/0.50          | ((X17)
% 0.21/0.50              = (k4_mcart_1 @ (k8_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 0.21/0.50                 (k9_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 0.21/0.50                 (k10_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17) @ 
% 0.21/0.50                 (k11_mcart_1 @ X13 @ X14 @ X15 @ X16 @ X17)))
% 0.21/0.50          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X13 @ X14 @ X15 @ X16))
% 0.21/0.50          | ((X16) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((sk_F_1)
% 0.21/0.50            = (k4_mcart_1 @ 
% 0.21/0.50               (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t61_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.21/0.50          ( ~( ![E:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.21/0.50                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.50                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.21/0.50                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.21/0.50                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ((X20) = (k1_xboole_0))
% 0.21/0.50          | ((k9_mcart_1 @ X18 @ X19 @ X20 @ X22 @ X21)
% 0.21/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X21))))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k4_zfmisc_1 @ X18 @ X19 @ X20 @ X22))
% 0.21/0.50          | ((X22) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.50  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ((X20) = (k1_xboole_0))
% 0.21/0.50          | ((k10_mcart_1 @ X18 @ X19 @ X20 @ X22 @ X21)
% 0.21/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X21)))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k4_zfmisc_1 @ X18 @ X19 @ X20 @ X22))
% 0.21/0.50          | ((X22) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['13', '14', '15', '16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.50         (((X18) = (k1_xboole_0))
% 0.21/0.50          | ((X19) = (k1_xboole_0))
% 0.21/0.50          | ((X20) = (k1_xboole_0))
% 0.21/0.50          | ((k11_mcart_1 @ X18 @ X19 @ X20 @ X22 @ X21) = (k2_mcart_1 @ X21))
% 0.21/0.50          | ~ (m1_subset_1 @ X21 @ (k4_zfmisc_1 @ X18 @ X19 @ X20 @ X22))
% 0.21/0.50          | ((X22) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50            = (k2_mcart_1 @ sk_F_1))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.50  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('25', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50         = (k2_mcart_1 @ sk_F_1))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['21', '22', '23', '24', '25'])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((sk_F_1)
% 0.21/0.50            = (k4_mcart_1 @ 
% 0.21/0.50               (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.21/0.50               (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['2', '10', '18', '26'])).
% 0.21/0.50  thf('28', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('29', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('31', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) @ 
% 0.21/0.50            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.21/0.50            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['27', '28', '29', '30', '31'])).
% 0.21/0.50  thf(t33_mcart_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.21/0.50     ( ( ( k4_mcart_1 @ A @ B @ C @ D ) = ( k4_mcart_1 @ E @ F @ G @ H ) ) =>
% 0.21/0.50       ( ( ( A ) = ( E ) ) & ( ( B ) = ( F ) ) & ( ( C ) = ( G ) ) & 
% 0.21/0.50         ( ( D ) = ( H ) ) ) ))).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, 
% 0.21/0.50         X12 : $i]:
% 0.21/0.50         (((X12) = (X9))
% 0.21/0.50          | ((k4_mcart_1 @ X6 @ X10 @ X11 @ X12)
% 0.21/0.50              != (k4_mcart_1 @ X5 @ X7 @ X8 @ X9)))),
% 0.21/0.50      inference('cnf', [status(esa)], [t33_mcart_1])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X6 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (('#_fresh_sk4' @ (k4_mcart_1 @ X6 @ X10 @ X11 @ X12)) = (X12))),
% 0.21/0.50      inference('inj_rec', [status(thm)], ['33'])).
% 0.21/0.50  thf('35', plain, ((('#_fresh_sk4' @ sk_F_1) = (k2_mcart_1 @ sk_F_1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['32', '34'])).
% 0.21/0.50  thf('36', plain,
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
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | ((X3)
% 0.21/0.50              = (k4_mcart_1 @ (sk_F @ X3 @ X4 @ X2 @ X1 @ X0) @ 
% 0.21/0.50                 (sk_G @ X3 @ X4 @ X2 @ X1 @ X0) @ 
% 0.21/0.50                 (sk_H @ X3 @ X4 @ X2 @ X1 @ X0) @ 
% 0.21/0.50                 (sk_I @ X3 @ X4 @ X2 @ X1 @ X0)))
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | ((sk_F_1)
% 0.21/0.50            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('40', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['38', '39', '40', '41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['38', '39', '40', '41', '42'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_G @ X3 @ X4 @ X2 @ X1 @ X0) @ X1)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.50  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['47', '48', '49', '50', '51'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X23 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X24 @ sk_D)
% 0.21/0.50          | ((sk_E) = (X24))
% 0.21/0.50          | ((sk_F_1) != (k4_mcart_1 @ X25 @ X23 @ X26 @ X24))
% 0.21/0.50          | ~ (m1_subset_1 @ X26 @ sk_C)
% 0.21/0.50          | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.21/0.50          | ((sk_F_1)
% 0.21/0.50              != (k4_mcart_1 @ X0 @ 
% 0.21/0.50                  (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ X1 @ X2))
% 0.21/0.50          | ((sk_E) = (X2))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      ((((sk_F_1) != (sk_F_1))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.50        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '54'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_I @ X3 @ X4 @ X2 @ X1 @ X0) @ X4)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.50  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('61', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['58', '59', '60', '61', '62'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_H @ X3 @ X4 @ X2 @ X1 @ X0) @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('68', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('70', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['66', '67', '68', '69', '70'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.50         (((X0) = (k1_xboole_0))
% 0.21/0.50          | ((X1) = (k1_xboole_0))
% 0.21/0.50          | ((X2) = (k1_xboole_0))
% 0.21/0.50          | (m1_subset_1 @ (sk_F @ X3 @ X4 @ X2 @ X1 @ X0) @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X3 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X4))
% 0.21/0.50          | ((X4) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((((sk_D) = (k1_xboole_0))
% 0.21/0.50        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.21/0.50        | ((sk_C) = (k1_xboole_0))
% 0.21/0.50        | ((sk_B) = (k1_xboole_0))
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('76', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('78', plain, (((sk_D) != (k1_xboole_0))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['74', '75', '76', '77', '78'])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      ((((sk_F_1) != (sk_F_1))
% 0.21/0.50        | ((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['55', '63', '71', '79'])).
% 0.21/0.50  thf('81', plain, (((sk_E) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['80'])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (((sk_F_1)
% 0.21/0.50         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.21/0.50            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))),
% 0.21/0.50      inference('demod', [status(thm)], ['43', '81'])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      (![X6 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.50         (('#_fresh_sk4' @ (k4_mcart_1 @ X6 @ X10 @ X11 @ X12)) = (X12))),
% 0.21/0.50      inference('inj_rec', [status(thm)], ['33'])).
% 0.21/0.50  thf('84', plain, ((('#_fresh_sk4' @ sk_F_1) = (sk_E))),
% 0.21/0.50      inference('sup+', [status(thm)], ['82', '83'])).
% 0.21/0.50  thf('85', plain, (((sk_E) = (k2_mcart_1 @ sk_F_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['35', '84'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.21/0.50         = (k2_mcart_1 @ sk_F_1))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)],
% 0.21/0.50                ['21', '22', '23', '24', '25'])).
% 0.21/0.50  thf('88', plain, (((sk_E) != (k2_mcart_1 @ sk_F_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['86', '87'])).
% 0.21/0.50  thf('89', plain, ($false),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['85', '88'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
