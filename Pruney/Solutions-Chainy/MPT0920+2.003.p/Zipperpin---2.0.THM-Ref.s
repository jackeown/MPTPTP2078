%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GCxIyaBQmA

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:11 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  124 (1029 expanded)
%              Number of leaves         :   28 ( 334 expanded)
%              Depth                    :   21
%              Number of atoms          : 1340 (27344 expanded)
%              Number of equality atoms :  167 (3639 expanded)
%              Maximal formula depth    :   26 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X19 @ X20 @ X21 @ X23 @ X22 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X22 ) ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17
        = ( k4_mcart_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('5',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F_1
      = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
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
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('11',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf(d4_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_mcart_1 @ A @ B @ C @ D )
      = ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('13',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k2_mcart_1 @ sk_F_1 )
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_mcart_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k4_tarski @ ( k3_mcart_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_mcart_1])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_mcart_1 @ ( k4_mcart_1 @ X3 @ X2 @ X1 @ X0 ) )
      = ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k1_mcart_1 @ sk_F_1 )
    = ( k3_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('23',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['16','25'])).

thf('27',plain,
    ( ( k1_mcart_1 @ sk_F_1 )
    = ( k3_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('28',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('29',plain,
    ( ( k1_mcart_1 @ sk_F_1 )
    = ( k3_mcart_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = ( k4_tarski @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X24 @ X25 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('35',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['26','35'])).

thf('37',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( k4_tarski @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('38',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('39',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X24: $i,X26: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X24 @ X26 ) )
      = X26 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('41',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_F_1
    = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ ( k2_mcart_1 @ sk_F_1 ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_G @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('45',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('47',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

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
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ~ ( m1_subset_1 @ X28 @ sk_D )
      | ( sk_F_1
       != ( k4_mcart_1 @ X29 @ X27 @ X30 @ X28 ) )
      | ( sk_E = X27 )
      | ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) )
      | ( sk_F_1
       != ( k4_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_F_1 ) @ sk_D )
    | ( sk_E
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['42','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_I @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('58',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_mcart_1 @ sk_F_1 )
    = ( sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('60',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( k2_mcart_1 @ sk_F_1 ) @ sk_D )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_F_1 ) @ sk_D ),
    inference('simplify_reflect-',[status(thm)],['60','61','62','63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_H @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('68',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['68','69','70','71','72'])).

thf('74',plain,
    ( ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) )
    = ( sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf('75',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) @ sk_C ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_F_1 @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_F @ X17 @ X18 @ X16 @ X15 @ X14 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l68_mcart_1])).

thf('78',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['78','79','80','81','82'])).

thf('84',plain,
    ( ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) )
    = ( sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('85',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_F_1 != sk_F_1 )
    | ( sk_E
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ) ),
    inference(demod,[status(thm)],['55','65','75','85'])).

thf('87',plain,
    ( sk_E
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F_1 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 )
      = sk_E )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','87'])).

thf('89',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','89','90','91','92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GCxIyaBQmA
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:52:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 106 iterations in 0.080s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.34/0.53  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.34/0.53  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.34/0.53  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.34/0.53  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.34/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.34/0.53  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.53  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.53  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.34/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.53  thf(t80_mcart_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.34/0.53     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.34/0.53       ( ( ![G:$i]:
% 0.34/0.53           ( ( m1_subset_1 @ G @ A ) =>
% 0.34/0.53             ( ![H:$i]:
% 0.34/0.53               ( ( m1_subset_1 @ H @ B ) =>
% 0.34/0.53                 ( ![I:$i]:
% 0.34/0.53                   ( ( m1_subset_1 @ I @ C ) =>
% 0.34/0.53                     ( ![J:$i]:
% 0.34/0.53                       ( ( m1_subset_1 @ J @ D ) =>
% 0.34/0.53                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.34/0.53                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.34/0.53         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.34/0.53        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.34/0.53          ( ( ![G:$i]:
% 0.34/0.53              ( ( m1_subset_1 @ G @ A ) =>
% 0.34/0.53                ( ![H:$i]:
% 0.34/0.53                  ( ( m1_subset_1 @ H @ B ) =>
% 0.34/0.53                    ( ![I:$i]:
% 0.34/0.53                      ( ( m1_subset_1 @ I @ C ) =>
% 0.34/0.53                        ( ![J:$i]:
% 0.34/0.53                          ( ( m1_subset_1 @ J @ D ) =>
% 0.34/0.53                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.34/0.53                              ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.34/0.53            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.34/0.53              ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t80_mcart_1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(t61_mcart_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ~( ![E:$i]:
% 0.34/0.53               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.34/0.53                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.34/0.53                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.34/0.53                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.34/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.34/0.53                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.34/0.53                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.34/0.53                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.34/0.53         (((X19) = (k1_xboole_0))
% 0.34/0.53          | ((X20) = (k1_xboole_0))
% 0.34/0.53          | ((X21) = (k1_xboole_0))
% 0.34/0.53          | ((k9_mcart_1 @ X19 @ X20 @ X21 @ X23 @ X22)
% 0.34/0.53              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X22))))
% 0.34/0.53          | ~ (m1_subset_1 @ X22 @ (k4_zfmisc_1 @ X19 @ X20 @ X21 @ X23))
% 0.34/0.53          | ((X23) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1)
% 0.34/0.53            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['0', '1'])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf(l68_mcart_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.34/0.53          ( ?[E:$i]:
% 0.34/0.53            ( ( ![F:$i]:
% 0.34/0.53                ( ( m1_subset_1 @ F @ A ) =>
% 0.34/0.53                  ( ![G:$i]:
% 0.34/0.53                    ( ( m1_subset_1 @ G @ B ) =>
% 0.34/0.53                      ( ![H:$i]:
% 0.34/0.53                        ( ( m1_subset_1 @ H @ C ) =>
% 0.34/0.53                          ( ![I:$i]:
% 0.34/0.53                            ( ( m1_subset_1 @ I @ D ) =>
% 0.34/0.53                              ( ( E ) != ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ) ) ) ) & 
% 0.34/0.53              ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.53         (((X14) = (k1_xboole_0))
% 0.34/0.53          | ((X15) = (k1_xboole_0))
% 0.34/0.53          | ((X16) = (k1_xboole_0))
% 0.34/0.53          | ((X17)
% 0.34/0.53              = (k4_mcart_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.34/0.53                 (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.34/0.53                 (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ 
% 0.34/0.53                 (sk_I @ X17 @ X18 @ X16 @ X15 @ X14)))
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.34/0.53          | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | ((sk_F_1)
% 0.34/0.53            = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53               (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53               (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53               (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.34/0.53  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.34/0.53  thf(d4_mcart_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.53     ( ( k4_mcart_1 @ A @ B @ C @ D ) =
% 0.34/0.53       ( k4_tarski @ ( k3_mcart_1 @ A @ B @ C ) @ D ) ))).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.53         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.34/0.53           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.34/0.53  thf(t7_mcart_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.34/0.53       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         ((k2_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0)) = (X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['12', '13'])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (((k2_mcart_1 @ sk_F_1) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['11', '14'])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_F_1)))),
% 0.34/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ (k2_mcart_1 @ sk_F_1)))),
% 0.34/0.53      inference('demod', [status(thm)], ['10', '15'])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.53         ((k4_mcart_1 @ X6 @ X7 @ X8 @ X9)
% 0.34/0.53           = (k4_tarski @ (k3_mcart_1 @ X6 @ X7 @ X8) @ X9))),
% 0.34/0.53      inference('cnf', [status(esa)], [d4_mcart_1])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.34/0.53         ((k1_mcart_1 @ (k4_mcart_1 @ X3 @ X2 @ X1 @ X0))
% 0.34/0.53           = (k3_mcart_1 @ X3 @ X2 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (((k1_mcart_1 @ sk_F_1)
% 0.34/0.53         = (k3_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.34/0.53  thf(d3_mcart_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.34/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('24', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.34/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.34/0.53  thf('25', plain,
% 0.34/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.34/0.53         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['21', '24'])).
% 0.34/0.53  thf('26', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.34/0.53      inference('demod', [status(thm)], ['16', '25'])).
% 0.34/0.53  thf('27', plain,
% 0.34/0.53      (((k1_mcart_1 @ sk_F_1)
% 0.34/0.53         = (k3_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['17', '20'])).
% 0.34/0.53  thf('28', plain,
% 0.34/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.34/0.53         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['21', '24'])).
% 0.34/0.53  thf('29', plain,
% 0.34/0.53      (((k1_mcart_1 @ sk_F_1)
% 0.34/0.53         = (k3_mcart_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.34/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.34/0.53  thf('30', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.34/0.53           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.34/0.53      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.34/0.53  thf('31', plain,
% 0.34/0.53      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('32', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         ((k1_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (k4_tarski @ X2 @ X1))),
% 0.34/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.34/0.53  thf('33', plain,
% 0.34/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.34/0.53         = (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['29', '32'])).
% 0.34/0.53  thf('34', plain,
% 0.34/0.53      (![X24 : $i, X25 : $i]: ((k1_mcart_1 @ (k4_tarski @ X24 @ X25)) = (X24))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('35', plain,
% 0.34/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.34/0.53         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.34/0.53  thf('36', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.34/0.53      inference('demod', [status(thm)], ['26', '35'])).
% 0.34/0.53  thf('37', plain,
% 0.34/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.34/0.53         = (k4_tarski @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('sup+', [status(thm)], ['29', '32'])).
% 0.34/0.53  thf('38', plain,
% 0.34/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.34/0.53         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.34/0.53  thf('39', plain,
% 0.34/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.34/0.53         = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53            (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.34/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.34/0.53  thf('40', plain,
% 0.34/0.53      (![X24 : $i, X26 : $i]: ((k2_mcart_1 @ (k4_tarski @ X24 @ X26)) = (X26))),
% 0.34/0.53      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.53  thf('41', plain,
% 0.34/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.34/0.53         = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.34/0.53  thf('42', plain,
% 0.34/0.53      (((sk_F_1)
% 0.34/0.53         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53            (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ (k2_mcart_1 @ sk_F_1)))),
% 0.34/0.53      inference('demod', [status(thm)], ['36', '41'])).
% 0.34/0.53  thf('43', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('44', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.53         (((X14) = (k1_xboole_0))
% 0.34/0.53          | ((X15) = (k1_xboole_0))
% 0.34/0.53          | ((X16) = (k1_xboole_0))
% 0.34/0.53          | (m1_subset_1 @ (sk_G @ X17 @ X18 @ X16 @ X15 @ X14) @ X15)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.34/0.53          | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.34/0.53  thf('45', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | (m1_subset_1 @ (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.53  thf('46', plain,
% 0.34/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.34/0.53         = (sk_G @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['39', '40'])).
% 0.34/0.53  thf('47', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53           sk_B)
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['45', '46'])).
% 0.34/0.53  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('52', plain,
% 0.34/0.53      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53        sk_B)),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)],
% 0.34/0.53                ['47', '48', '49', '50', '51'])).
% 0.34/0.53  thf('53', plain,
% 0.34/0.53      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X27 @ sk_B)
% 0.34/0.53          | ~ (m1_subset_1 @ X28 @ sk_D)
% 0.34/0.53          | ((sk_F_1) != (k4_mcart_1 @ X29 @ X27 @ X30 @ X28))
% 0.34/0.53          | ((sk_E) = (X27))
% 0.34/0.53          | ~ (m1_subset_1 @ X30 @ sk_C)
% 0.34/0.53          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('54', plain,
% 0.34/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.53         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.34/0.53          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.34/0.53          | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))
% 0.34/0.53          | ((sk_F_1)
% 0.34/0.53              != (k4_mcart_1 @ X0 @ 
% 0.34/0.53                  (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ X1 @ X2))
% 0.34/0.53          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.34/0.53      inference('sup-', [status(thm)], ['52', '53'])).
% 0.34/0.53  thf('55', plain,
% 0.34/0.53      ((((sk_F_1) != (sk_F_1))
% 0.34/0.53        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_F_1) @ sk_D)
% 0.34/0.53        | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))
% 0.34/0.53        | ~ (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ sk_C)
% 0.34/0.53        | ~ (m1_subset_1 @ 
% 0.34/0.53             (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ sk_A))),
% 0.34/0.53      inference('sup-', [status(thm)], ['42', '54'])).
% 0.34/0.53  thf('56', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('57', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.53         (((X14) = (k1_xboole_0))
% 0.34/0.53          | ((X15) = (k1_xboole_0))
% 0.34/0.53          | ((X16) = (k1_xboole_0))
% 0.34/0.53          | (m1_subset_1 @ (sk_I @ X17 @ X18 @ X16 @ X15 @ X14) @ X18)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.34/0.53          | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.34/0.53  thf('58', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | (m1_subset_1 @ (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.34/0.53  thf('59', plain,
% 0.34/0.53      (((k2_mcart_1 @ sk_F_1) = (sk_I @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['11', '14'])).
% 0.34/0.53  thf('60', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | (m1_subset_1 @ (k2_mcart_1 @ sk_F_1) @ sk_D)
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.34/0.53  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('64', plain, (((sk_D) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('65', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_F_1) @ sk_D)),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)],
% 0.34/0.53                ['60', '61', '62', '63', '64'])).
% 0.34/0.53  thf('66', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('67', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.53         (((X14) = (k1_xboole_0))
% 0.34/0.53          | ((X15) = (k1_xboole_0))
% 0.34/0.53          | ((X16) = (k1_xboole_0))
% 0.34/0.53          | (m1_subset_1 @ (sk_H @ X17 @ X18 @ X16 @ X15 @ X14) @ X16)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.34/0.53          | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.34/0.53  thf('68', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | (m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['66', '67'])).
% 0.34/0.53  thf('69', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('70', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('71', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('72', plain, (((sk_D) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('73', plain,
% 0.34/0.53      ((m1_subset_1 @ (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)],
% 0.34/0.53                ['68', '69', '70', '71', '72'])).
% 0.34/0.53  thf('74', plain,
% 0.34/0.53      (((k2_mcart_1 @ (k1_mcart_1 @ sk_F_1))
% 0.34/0.53         = (sk_H @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['21', '24'])).
% 0.34/0.53  thf('75', plain,
% 0.34/0.53      ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F_1)) @ sk_C)),
% 0.34/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.34/0.53  thf('76', plain,
% 0.34/0.53      ((m1_subset_1 @ sk_F_1 @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('77', plain,
% 0.34/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.34/0.53         (((X14) = (k1_xboole_0))
% 0.34/0.53          | ((X15) = (k1_xboole_0))
% 0.34/0.53          | ((X16) = (k1_xboole_0))
% 0.34/0.53          | (m1_subset_1 @ (sk_F @ X17 @ X18 @ X16 @ X15 @ X14) @ X14)
% 0.34/0.53          | ~ (m1_subset_1 @ X17 @ (k4_zfmisc_1 @ X14 @ X15 @ X16 @ X18))
% 0.34/0.53          | ((X18) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [l68_mcart_1])).
% 0.34/0.53  thf('78', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | (m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['76', '77'])).
% 0.34/0.53  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('80', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('81', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('82', plain, (((sk_D) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('83', plain,
% 0.34/0.53      ((m1_subset_1 @ (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)],
% 0.34/0.53                ['78', '79', '80', '81', '82'])).
% 0.34/0.53  thf('84', plain,
% 0.34/0.53      (((k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))
% 0.34/0.53         = (sk_F @ sk_F_1 @ sk_D @ sk_C @ sk_B @ sk_A))),
% 0.34/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.34/0.53  thf('85', plain,
% 0.34/0.53      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))) @ 
% 0.34/0.53        sk_A)),
% 0.34/0.53      inference('demod', [status(thm)], ['83', '84'])).
% 0.34/0.53  thf('86', plain,
% 0.34/0.53      ((((sk_F_1) != (sk_F_1))
% 0.34/0.53        | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1)))))),
% 0.34/0.53      inference('demod', [status(thm)], ['55', '65', '75', '85'])).
% 0.34/0.53  thf('87', plain,
% 0.34/0.53      (((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F_1))))),
% 0.34/0.53      inference('simplify', [status(thm)], ['86'])).
% 0.34/0.53  thf('88', plain,
% 0.34/0.53      ((((sk_D) = (k1_xboole_0))
% 0.34/0.53        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1) = (sk_E))
% 0.34/0.53        | ((sk_C) = (k1_xboole_0))
% 0.34/0.53        | ((sk_B) = (k1_xboole_0))
% 0.34/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['2', '87'])).
% 0.34/0.53  thf('89', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('90', plain, (((sk_B) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('91', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('92', plain,
% 0.34/0.53      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F_1))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('93', plain, (((sk_D) != (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('94', plain, ($false),
% 0.34/0.53      inference('simplify_reflect-', [status(thm)],
% 0.34/0.53                ['88', '89', '90', '91', '92', '93'])).
% 0.34/0.53  
% 0.34/0.53  % SZS output end Refutation
% 0.34/0.53  
% 0.34/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
