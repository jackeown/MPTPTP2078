%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvkE3G47xW

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:15 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  156 (2119 expanded)
%              Number of leaves         :   28 ( 676 expanded)
%              Depth                    :   30
%              Number of atoms          : 2487 (49893 expanded)
%              Number of equality atoms :  316 (6488 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_J_type,type,(
    sk_J: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_zfmisc_1 @ X0 @ X1 @ X2 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t80_mcart_1,axiom,(
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

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X3 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 @ X3 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X23 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

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

thf('14',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X10 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X10 ) ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','22'])).

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
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('30',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X25
        = ( k4_mcart_1 @ ( sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ ( sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ ( sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ ( sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( X25
        = ( k4_mcart_1 @ ( sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ ( sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ ( sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ ( sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
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
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('54',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('55',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X22 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
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
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62','63'])).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ sk_B )
      | ~ ( m1_subset_1 @ X28 @ sk_D )
      | ( sk_E = X28 )
      | ( sk_F
       != ( k4_mcart_1 @ X29 @ X27 @ X30 @ X28 ) )
      | ~ ( m1_subset_1 @ X30 @ sk_C )
      | ~ ( m1_subset_1 @ X29 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_C )
      | ( sk_F
       != ( k4_mcart_1 @ X1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X2 @ X3 ) )
      | ( sk_E = X3 )
      | ~ ( m1_subset_1 @ X3 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( sk_F != sk_F )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['52','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('74',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('75',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 @ X24 ) )
      | ( X26
        = ( k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25 ) )
      | ( m1_subset_1 @ ( sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21 ) @ X24 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20','21'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['79','80','81','82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_E
        = ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['72','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['47','48','49','50','51'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

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

thf('91',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X15 @ X14 @ X13 @ X12 ) )
      | ( ( k11_mcart_1 @ X15 @ X14 @ X13 @ X12 @ X16 )
        = X17 )
      | ( X16
       != ( k4_mcart_1 @ X18 @ X19 @ X20 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('92',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k11_mcart_1 @ X15 @ X14 @ X13 @ X12 @ ( k4_mcart_1 @ X18 @ X19 @ X20 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X18 @ X19 @ X20 @ X17 ) @ ( k4_zfmisc_1 @ X15 @ X14 @ X13 @ X12 ) )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('94',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k11_mcart_1 @ X15 @ X14 @ X13 @ X12 @ ( k4_mcart_1 @ X18 @ X19 @ X20 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X18 @ X19 @ X20 @ X17 ) @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) @ X13 @ X12 ) )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) @ X1 @ X0 ) )
      | ( X4
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['90','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','95'])).

thf('97',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E ) )
        = sk_E )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['96','97','98','99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ) ) ),
    inference('sup+',[status(thm)],['88','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
      | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('105',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
     != sk_E )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = sk_E ) ),
    inference(eq_fact,[status(thm)],['104'])).

thf('106',plain,(
    m1_subset_1 @ sk_F @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('107',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10 )
        = ( k2_mcart_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('108',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6 )
      = ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('109',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10 )
        = ( k2_mcart_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k3_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) @ X9 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
    ( ( ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
     != sk_E )
    | ( ( k2_mcart_1 @ sk_F )
      = sk_E ) ),
    inference(demod,[status(thm)],['105','115'])).

thf('117',plain,(
    sk_E
 != ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['110','111','112','113','114'])).

thf('119',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
 != sk_E ),
    inference('simplify_reflect-',[status(thm)],['116','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_E )
      | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['103','120'])).

thf('122',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['110','111','112','113','114'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_E )
      | ( ( k2_mcart_1 @ sk_F )
        = sk_E ) ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_mcart_1 @ sk_F )
    = sk_E ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    sk_E
 != ( k2_mcart_1 @ sk_F ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('126',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jvkE3G47xW
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:19:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 100 iterations in 0.221s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.45/0.68  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(sk_J_type, type, sk_J: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(sk_F_type, type, sk_F: $i).
% 0.45/0.68  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.45/0.68  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.68  thf(t82_mcart_1, conjecture,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.68       ( ( ![G:$i]:
% 0.45/0.68           ( ( m1_subset_1 @ G @ A ) =>
% 0.45/0.68             ( ![H:$i]:
% 0.45/0.68               ( ( m1_subset_1 @ H @ B ) =>
% 0.45/0.68                 ( ![I:$i]:
% 0.45/0.68                   ( ( m1_subset_1 @ I @ C ) =>
% 0.45/0.68                     ( ![J:$i]:
% 0.45/0.68                       ( ( m1_subset_1 @ J @ D ) =>
% 0.45/0.68                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.45/0.68                           ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.45/0.68         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68           ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.68        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.68          ( ( ![G:$i]:
% 0.45/0.68              ( ( m1_subset_1 @ G @ A ) =>
% 0.45/0.68                ( ![H:$i]:
% 0.45/0.68                  ( ( m1_subset_1 @ H @ B ) =>
% 0.45/0.68                    ( ![I:$i]:
% 0.45/0.68                      ( ( m1_subset_1 @ I @ C ) =>
% 0.45/0.68                        ( ![J:$i]:
% 0.45/0.68                          ( ( m1_subset_1 @ J @ D ) =>
% 0.45/0.68                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.45/0.68                              ( ( E ) = ( J ) ) ) ) ) ) ) ) ) ) ) =>
% 0.45/0.68            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68              ( ( E ) = ( k11_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t82_mcart_1])).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(d4_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.45/0.68       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf(d3_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.45/0.68       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.45/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ X0 @ X1 @ X2)
% 0.45/0.68           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1) @ X2))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.45/0.68  thf('5', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.68           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.45/0.68      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf(t80_mcart_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.68       ( ( ![G:$i]:
% 0.45/0.68           ( ( m1_subset_1 @ G @ A ) =>
% 0.45/0.68             ( ![H:$i]:
% 0.45/0.68               ( ( m1_subset_1 @ H @ B ) =>
% 0.45/0.68                 ( ![I:$i]:
% 0.45/0.68                   ( ( m1_subset_1 @ I @ C ) =>
% 0.45/0.68                     ( ![J:$i]:
% 0.45/0.68                       ( ( m1_subset_1 @ J @ D ) =>
% 0.45/0.68                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.45/0.68                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.45/0.68         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.45/0.68           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ (k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X23))),
% 0.45/0.68      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X3 @ X4 @ X5) @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         ((k3_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0 @ X3)
% 0.45/0.68           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ X3))),
% 0.45/0.68      inference('sup+', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X23))),
% 0.45/0.68      inference('demod', [status(thm)], ['7', '10'])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.45/0.68          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['6', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf(t61_mcart_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68          ( ~( ![E:$i]:
% 0.45/0.68               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.68                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.68                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.45/0.68                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.68                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.45/0.68                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.45/0.68                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.45/0.68                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((X7) = (k1_xboole_0))
% 0.45/0.68          | ((X8) = (k1_xboole_0))
% 0.45/0.68          | ((X9) = (k1_xboole_0))
% 0.45/0.68          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10)
% 0.45/0.68              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X10))))
% 0.45/0.68          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.45/0.68          | ((X11) = (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((X7) = (k1_xboole_0))
% 0.45/0.68          | ((X8) = (k1_xboole_0))
% 0.45/0.68          | ((X9) = (k1_xboole_0))
% 0.45/0.68          | ((k9_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10)
% 0.45/0.68              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X10))))
% 0.45/0.68          | ~ (m1_subset_1 @ X10 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9 @ X11))
% 0.45/0.68          | ((X11) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['14', '15'])).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      ((((sk_D) = (k1_xboole_0))
% 0.45/0.68        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68        | ((sk_C) = (k1_xboole_0))
% 0.45/0.68        | ((sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.68  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('20', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('21', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['17', '18', '19', '20', '21'])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['12', '22'])).
% 0.45/0.68  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('26', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('27', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['23', '24', '25', '26', '27'])).
% 0.45/0.68  thf('29', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ (k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X21))),
% 0.45/0.68      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X21))),
% 0.45/0.68      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.45/0.68          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['29', '32'])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['17', '18', '19', '20', '21'])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.68  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('38', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('39', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['35', '36', '37', '38', '39'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ (k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | ((X25)
% 0.45/0.68              = (k4_mcart_1 @ (sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ 
% 0.45/0.68                 (sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ 
% 0.45/0.68                 (sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ 
% 0.45/0.68                 (sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21))))),
% 0.45/0.68      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | ((X25)
% 0.45/0.68              = (k4_mcart_1 @ (sk_G @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ 
% 0.45/0.68                 (sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ 
% 0.45/0.68                 (sk_I @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ 
% 0.45/0.68                 (sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21))))),
% 0.45/0.68      inference('demod', [status(thm)], ['42', '43'])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_F)
% 0.45/0.68            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.45/0.68          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['41', '44'])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['17', '18', '19', '20', '21'])).
% 0.45/0.68  thf('47', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_F)
% 0.45/0.68            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.45/0.68  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('50', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('51', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_F)
% 0.45/0.68            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['47', '48', '49', '50', '51'])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ (k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X22))),
% 0.45/0.68      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_H @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X22))),
% 0.45/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.45/0.68          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['53', '56'])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['17', '18', '19', '20', '21'])).
% 0.45/0.68  thf('59', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.68  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('61', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('63', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('64', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['59', '60', '61', '62', '63'])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X27 @ sk_B)
% 0.45/0.68          | ~ (m1_subset_1 @ X28 @ sk_D)
% 0.45/0.68          | ((sk_E) = (X28))
% 0.45/0.68          | ((sk_F) != (k4_mcart_1 @ X29 @ X27 @ X30 @ X28))
% 0.45/0.68          | ~ (m1_subset_1 @ X30 @ sk_C)
% 0.45/0.68          | ~ (m1_subset_1 @ X29 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.45/0.68          | ~ (m1_subset_1 @ X2 @ sk_C)
% 0.45/0.68          | ((sk_F)
% 0.45/0.68              != (k4_mcart_1 @ X1 @ 
% 0.45/0.68                  (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ X2 @ X3))
% 0.45/0.68          | ((sk_E) = (X3))
% 0.45/0.68          | ~ (m1_subset_1 @ X3 @ sk_D))),
% 0.45/0.68      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_F) != (sk_F))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_D)
% 0.45/0.68          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_C)
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_A)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['52', '66'])).
% 0.45/0.68  thf('68', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68             sk_A)
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_C)
% 0.45/0.68          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_D)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['67'])).
% 0.45/0.68  thf('69', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_D)
% 0.45/0.68          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_C))),
% 0.45/0.68      inference('sup-', [status(thm)], ['40', '68'])).
% 0.45/0.68  thf('70', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68             sk_C)
% 0.45/0.68          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_D)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['69'])).
% 0.45/0.68  thf('71', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_D)
% 0.45/0.68          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['28', '70'])).
% 0.45/0.68  thf('72', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.45/0.68          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               sk_D)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.68  thf('73', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf('74', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ (k4_zfmisc_1 @ X21 @ X22 @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X24))),
% 0.45/0.68      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.45/0.68  thf('75', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('76', plain,
% 0.45/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.45/0.68         (((X21) = (k1_xboole_0))
% 0.45/0.68          | ((X22) = (k1_xboole_0))
% 0.45/0.68          | ((X23) = (k1_xboole_0))
% 0.45/0.68          | ((X24) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X25 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23 @ X24))
% 0.45/0.68          | ((X26) = (k9_mcart_1 @ X21 @ X22 @ X23 @ X24 @ X25))
% 0.45/0.68          | (m1_subset_1 @ (sk_J @ X25 @ X26 @ X24 @ X23 @ X22 @ X21) @ X24))),
% 0.45/0.68      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.68  thf('77', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.45/0.68          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['73', '76'])).
% 0.45/0.68  thf('78', plain,
% 0.45/0.68      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['17', '18', '19', '20', '21'])).
% 0.45/0.68  thf('79', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.68  thf('80', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('81', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('82', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('83', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('84', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['79', '80', '81', '82', '83'])).
% 0.45/0.68  thf('85', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_E) = (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['72', '84'])).
% 0.45/0.68  thf('86', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_F)
% 0.45/0.68            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['47', '48', '49', '50', '51'])).
% 0.45/0.68  thf('87', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((sk_F)
% 0.45/0.68            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['85', '86'])).
% 0.45/0.68  thf('88', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_F)
% 0.45/0.68              = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68                 (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68                 (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['87'])).
% 0.45/0.68  thf('89', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf('90', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((sk_F)
% 0.45/0.68              = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68                 (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68                 (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['87'])).
% 0.45/0.68  thf(t78_mcart_1, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.68     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.45/0.68       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.45/0.68            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.45/0.68              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.45/0.68                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.45/0.68                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.45/0.68                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.45/0.68                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.45/0.68  thf('91', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 0.45/0.68         X19 : $i, X20 : $i]:
% 0.45/0.68         (((X12) = (k1_xboole_0))
% 0.45/0.68          | ((X13) = (k1_xboole_0))
% 0.45/0.68          | ((X14) = (k1_xboole_0))
% 0.45/0.68          | ((X15) = (k1_xboole_0))
% 0.45/0.68          | ~ (m1_subset_1 @ X16 @ (k4_zfmisc_1 @ X15 @ X14 @ X13 @ X12))
% 0.45/0.68          | ((k11_mcart_1 @ X15 @ X14 @ X13 @ X12 @ X16) = (X17))
% 0.45/0.68          | ((X16) != (k4_mcart_1 @ X18 @ X19 @ X20 @ X17)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.45/0.68  thf('92', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.45/0.68         X20 : $i]:
% 0.45/0.68         (((k11_mcart_1 @ X15 @ X14 @ X13 @ X12 @ 
% 0.45/0.68            (k4_mcart_1 @ X18 @ X19 @ X20 @ X17)) = (X17))
% 0.45/0.68          | ~ (m1_subset_1 @ (k4_mcart_1 @ X18 @ X19 @ X20 @ X17) @ 
% 0.45/0.68               (k4_zfmisc_1 @ X15 @ X14 @ X13 @ X12))
% 0.45/0.68          | ((X15) = (k1_xboole_0))
% 0.45/0.68          | ((X14) = (k1_xboole_0))
% 0.45/0.68          | ((X13) = (k1_xboole_0))
% 0.45/0.68          | ((X12) = (k1_xboole_0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['91'])).
% 0.45/0.68  thf('93', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('94', plain,
% 0.45/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X17 : $i, X18 : $i, X19 : $i, 
% 0.45/0.68         X20 : $i]:
% 0.45/0.68         (((k11_mcart_1 @ X15 @ X14 @ X13 @ X12 @ 
% 0.45/0.68            (k4_mcart_1 @ X18 @ X19 @ X20 @ X17)) = (X17))
% 0.45/0.68          | ~ (m1_subset_1 @ (k4_mcart_1 @ X18 @ X19 @ X20 @ X17) @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14) @ X13 @ X12))
% 0.45/0.68          | ((X15) = (k1_xboole_0))
% 0.45/0.68          | ((X14) = (k1_xboole_0))
% 0.45/0.68          | ((X13) = (k1_xboole_0))
% 0.45/0.68          | ((X12) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.68  thf('95', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ sk_F @ 
% 0.45/0.68             (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2) @ X1 @ X0))
% 0.45/0.68          | ((X4) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((X0) = (k1_xboole_0))
% 0.45/0.68          | ((X1) = (k1_xboole_0))
% 0.45/0.68          | ((X2) = (k1_xboole_0))
% 0.45/0.68          | ((X3) = (k1_xboole_0))
% 0.45/0.68          | ((k11_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.45/0.68              (k4_mcart_1 @ (sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68               (sk_I @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.45/0.68              = (sk_E)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['90', '94'])).
% 0.45/0.68  thf('96', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.45/0.68            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.45/0.68            = (sk_E))
% 0.45/0.68          | ((sk_A) = (k1_xboole_0))
% 0.45/0.68          | ((sk_B) = (k1_xboole_0))
% 0.45/0.68          | ((sk_C) = (k1_xboole_0))
% 0.45/0.68          | ((sk_D) = (k1_xboole_0))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['89', '95'])).
% 0.45/0.68  thf('97', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('98', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('99', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('101', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.45/0.68            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.45/0.68             (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E))
% 0.45/0.68            = (sk_E))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['96', '97', '98', '99', '100'])).
% 0.45/0.68  thf('102', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F)))))),
% 0.45/0.68      inference('sup+', [status(thm)], ['88', '101'])).
% 0.45/0.68  thf('103', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['102'])).
% 0.45/0.68  thf('104', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.45/0.68          | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['102'])).
% 0.45/0.68  thf('105', plain,
% 0.45/0.68      ((((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) != (sk_E))
% 0.45/0.68        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.45/0.68      inference('eq_fact', [status(thm)], ['104'])).
% 0.45/0.68  thf('106', plain,
% 0.45/0.68      ((m1_subset_1 @ sk_F @ 
% 0.45/0.68        (k3_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C @ sk_D))),
% 0.45/0.68      inference('demod', [status(thm)], ['2', '5'])).
% 0.45/0.68  thf('107', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((X7) = (k1_xboole_0))
% 0.45/0.68          | ((X8) = (k1_xboole_0))
% 0.45/0.68          | ((X9) = (k1_xboole_0))
% 0.45/0.68          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10) = (k2_mcart_1 @ X10))
% 0.45/0.68          | ~ (m1_subset_1 @ X10 @ (k4_zfmisc_1 @ X7 @ X8 @ X9 @ X11))
% 0.45/0.68          | ((X11) = (k1_xboole_0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.45/0.68  thf('108', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.68         ((k4_zfmisc_1 @ X3 @ X4 @ X5 @ X6)
% 0.45/0.68           = (k3_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5 @ X6))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.68  thf('109', plain,
% 0.45/0.68      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.68         (((X7) = (k1_xboole_0))
% 0.45/0.68          | ((X8) = (k1_xboole_0))
% 0.45/0.68          | ((X9) = (k1_xboole_0))
% 0.45/0.68          | ((k11_mcart_1 @ X7 @ X8 @ X9 @ X11 @ X10) = (k2_mcart_1 @ X10))
% 0.45/0.68          | ~ (m1_subset_1 @ X10 @ 
% 0.45/0.68               (k3_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8) @ X9 @ X11))
% 0.45/0.68          | ((X11) = (k1_xboole_0)))),
% 0.45/0.68      inference('demod', [status(thm)], ['107', '108'])).
% 0.45/0.68  thf('110', plain,
% 0.45/0.68      ((((sk_D) = (k1_xboole_0))
% 0.45/0.68        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.45/0.68            = (k2_mcart_1 @ sk_F))
% 0.45/0.68        | ((sk_C) = (k1_xboole_0))
% 0.45/0.68        | ((sk_B) = (k1_xboole_0))
% 0.45/0.68        | ((sk_A) = (k1_xboole_0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['106', '109'])).
% 0.45/0.68  thf('111', plain, (((sk_A) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('112', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('113', plain, (((sk_C) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('114', plain, (((sk_D) != (k1_xboole_0))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('115', plain,
% 0.45/0.68      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['110', '111', '112', '113', '114'])).
% 0.45/0.68  thf('116', plain,
% 0.45/0.68      ((((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) != (sk_E))
% 0.45/0.68        | ((k2_mcart_1 @ sk_F) = (sk_E)))),
% 0.45/0.68      inference('demod', [status(thm)], ['105', '115'])).
% 0.45/0.68  thf('117', plain,
% 0.45/0.68      (((sk_E) != (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('118', plain,
% 0.45/0.68      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['110', '111', '112', '113', '114'])).
% 0.45/0.68  thf('119', plain, (((sk_E) != (k2_mcart_1 @ sk_F))),
% 0.45/0.68      inference('demod', [status(thm)], ['117', '118'])).
% 0.45/0.68  thf('120', plain,
% 0.45/0.68      (((k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) != (sk_E))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['116', '119'])).
% 0.45/0.68  thf('121', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0) != (sk_E))
% 0.45/0.68          | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['103', '120'])).
% 0.45/0.68  thf('122', plain,
% 0.45/0.68      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)],
% 0.45/0.68                ['110', '111', '112', '113', '114'])).
% 0.45/0.68  thf('123', plain,
% 0.45/0.68      (![X0 : $i]: (((X0) != (sk_E)) | ((k2_mcart_1 @ sk_F) = (sk_E)))),
% 0.45/0.68      inference('demod', [status(thm)], ['121', '122'])).
% 0.45/0.68  thf('124', plain, (((k2_mcart_1 @ sk_F) = (sk_E))),
% 0.45/0.68      inference('simplify', [status(thm)], ['123'])).
% 0.45/0.68  thf('125', plain, (((sk_E) != (k2_mcart_1 @ sk_F))),
% 0.45/0.68      inference('demod', [status(thm)], ['117', '118'])).
% 0.45/0.68  thf('126', plain, ($false),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
