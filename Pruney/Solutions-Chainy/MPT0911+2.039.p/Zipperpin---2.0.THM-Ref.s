%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cy6ITboJop

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:01 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 632 expanded)
%              Number of leaves         :   26 ( 205 expanded)
%              Depth                    :   23
%              Number of atoms          : 1876 (14211 expanded)
%              Number of equality atoms :  260 (2035 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i )).

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

thf(t69_mcart_1,axiom,(
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
                     => ( D = F ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X21 @ X22 @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( m1_subset_1 @ ( sk_F @ X24 @ X25 @ X23 @ X22 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_mcart_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('5',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( m1_subset_1 @ ( sk_F @ X24 @ X25 @ X23 @ X22 @ X21 ) @ X21 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X21 @ X22 @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X24
        = ( k3_mcart_1 @ ( sk_F @ X24 @ X25 @ X23 @ X22 @ X21 ) @ ( sk_G @ X24 @ X25 @ X23 @ X22 @ X21 ) @ ( sk_H @ X24 @ X25 @ X23 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t69_mcart_1])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( X24
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ X24 @ X25 @ X23 @ X22 @ X21 ) @ ( sk_G @ X24 @ X25 @ X23 @ X22 @ X21 ) ) @ ( sk_H @ X24 @ X25 @ X23 @ X22 @ X21 ) ) ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

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
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','29','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X21 @ X22 @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( m1_subset_1 @ ( sk_G @ X24 @ X25 @ X23 @ X22 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_mcart_1])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( m1_subset_1 @ ( sk_G @ X24 @ X25 @ X23 @ X22 @ X21 ) @ X22 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

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
      ( ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ( sk_E
       != ( k3_mcart_1 @ X27 @ X26 @ X28 ) )
      | ( sk_D = X28 )
      | ~ ( m1_subset_1 @ X28 @ sk_C )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('46',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X26 @ sk_B )
      | ( sk_E
       != ( k4_tarski @ ( k4_tarski @ X27 @ X26 ) @ X28 ) )
      | ( sk_D = X28 )
      | ~ ( m1_subset_1 @ X28 @ sk_C )
      | ~ ( m1_subset_1 @ X27 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_C )
      | ( sk_D = X2 )
      | ( sk_E
       != ( k4_tarski @ ( k4_tarski @ X1 @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_E != sk_E )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X21 @ X22 @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( m1_subset_1 @ ( sk_H @ X24 @ X25 @ X23 @ X22 @ X21 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_mcart_1])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X24 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) @ X23 ) )
      | ( X25
        = ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) )
      | ( m1_subset_1 @ ( sk_H @ X24 @ X25 @ X23 @ X22 @ X21 ) @ X23 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

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
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_D
        = ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ ( sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['28','29','30','31'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( sk_E
        = ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

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

thf('69',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X16 @ X15 @ X14 ) )
      | ( ( k7_mcart_1 @ X16 @ X15 @ X14 @ X17 )
        = X20 )
      | ( X17
       != ( k3_mcart_1 @ X18 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t68_mcart_1])).

thf('70',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_mcart_1 @ X16 @ X15 @ X14 @ ( k3_mcart_1 @ X18 @ X19 @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ ( k3_mcart_1 @ X18 @ X19 @ X20 ) @ ( k3_zfmisc_1 @ X16 @ X15 @ X14 ) )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X0 @ X1 @ X2 )
      = ( k4_tarski @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('74',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i,X19: $i,X20: $i] :
      ( ( ( k7_mcart_1 @ X16 @ X15 @ X14 @ ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) )
        = X20 )
      | ~ ( m1_subset_1 @ ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X15 ) @ X14 ) )
      | ( X16 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) @ X0 ) )
      | ( X3
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X2 @ X1 @ X0 @ ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X3 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X3 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
        = sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ ( k4_tarski @ ( k4_tarski @ ( sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) @ ( sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A ) ) @ sk_D ) )
        = sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup+',[status(thm)],['66','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
      | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t51_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( D
                 != ( k5_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k6_mcart_1 @ A @ B @ C @ D ) )
                & ( D
                 != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('84',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X13
       != ( k5_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X10 @ X11 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t51_mcart_1])).

thf('85',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('86',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ( X13
       != ( k5_mcart_1 @ X10 @ X11 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E
     != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('89',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E
     != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    sk_E
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['89','90','91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( sk_E != X0 )
      | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['82','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_E @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('96',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k3_zfmisc_1 @ X6 @ X7 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('97',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('98',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X6 @ X7 @ X9 @ X8 )
        = ( k2_mcart_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['99','100','101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( sk_E != X0 )
      | ( ( k2_mcart_1 @ sk_E )
        = sk_D ) ) ),
    inference(demod,[status(thm)],['94','103'])).

thf('105',plain,
    ( ( k2_mcart_1 @ sk_E )
    = sk_D ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['99','100','101','102'])).

thf('108',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Cy6ITboJop
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 51 iterations in 0.058s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.19/0.50  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.50  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.19/0.50  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i).
% 0.19/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i).
% 0.19/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(t71_mcart_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50       ( ( ![F:$i]:
% 0.19/0.50           ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.50             ( ![G:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.50                 ( ![H:$i]:
% 0.19/0.50                   ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.50                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.50                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.19/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.50        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50          ( ( ![F:$i]:
% 0.19/0.50              ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.50                ( ![G:$i]:
% 0.19/0.50                  ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.50                    ( ![H:$i]:
% 0.19/0.50                      ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.50                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.50                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 0.19/0.50            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 0.19/0.50  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(d3_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.19/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(t69_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50       ( ( ![F:$i]:
% 0.19/0.50           ( ( m1_subset_1 @ F @ A ) =>
% 0.19/0.50             ( ![G:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ G @ B ) =>
% 0.19/0.50                 ( ![H:$i]:
% 0.19/0.50                   ( ( m1_subset_1 @ H @ C ) =>
% 0.19/0.50                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.19/0.50                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.19/0.50         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X21 @ X22 @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | (m1_subset_1 @ (sk_F @ X24 @ X25 @ X23 @ X22 @ X21) @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_mcart_1])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ 
% 0.19/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | (m1_subset_1 @ (sk_F @ X24 @ X25 @ X23 @ X22 @ X21) @ X21))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50          | ((X0) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(t50_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ~( ![D:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.50                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.19/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.19/0.50                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (((X6) = (k1_xboole_0))
% 0.19/0.50          | ((X7) = (k1_xboole_0))
% 0.19/0.50          | ((k5_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.19/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.50          | ((X9) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (((X6) = (k1_xboole_0))
% 0.19/0.50          | ((X7) = (k1_xboole_0))
% 0.19/0.50          | ((k5_mcart_1 @ X6 @ X7 @ X9 @ X8)
% 0.19/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X8)))
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.19/0.50          | ((X9) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.19/0.50            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50        | ((sk_B) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.50  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('13', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.19/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['6', '15'])).
% 0.19/0.50  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('19', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X21 @ X22 @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | ((X24)
% 0.19/0.50              = (k3_mcart_1 @ (sk_F @ X24 @ X25 @ X23 @ X22 @ X21) @ 
% 0.19/0.50                 (sk_G @ X24 @ X25 @ X23 @ X22 @ X21) @ 
% 0.19/0.50                 (sk_H @ X24 @ X25 @ X23 @ X22 @ X21))))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_mcart_1])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf(d3_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.50           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ 
% 0.19/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | ((X24)
% 0.19/0.50              = (k4_tarski @ 
% 0.19/0.50                 (k4_tarski @ (sk_F @ X24 @ X25 @ X23 @ X22 @ X21) @ 
% 0.19/0.50                  (sk_G @ X24 @ X25 @ X23 @ X22 @ X21)) @ 
% 0.19/0.50                 (sk_H @ X24 @ X25 @ X23 @ X22 @ X21))))),
% 0.19/0.50      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E)
% 0.19/0.50            = (k4_tarski @ 
% 0.19/0.50               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.50          | ((X0) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['21', '25'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.19/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E)
% 0.19/0.50            = (k4_tarski @ 
% 0.19/0.50               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E)
% 0.19/0.50            = (k4_tarski @ 
% 0.19/0.50               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['28', '29', '30', '31'])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X21 @ X22 @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | (m1_subset_1 @ (sk_G @ X24 @ X25 @ X23 @ X22 @ X21) @ X22))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_mcart_1])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ 
% 0.19/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | (m1_subset_1 @ (sk_G @ X24 @ X25 @ X23 @ X22 @ X21) @ X22))),
% 0.19/0.50      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.50          | ((X0) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '36'])).
% 0.19/0.50  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('39', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('40', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.50          | ((X0) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38', '39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.19/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.50          | ((sk_E) != (k3_mcart_1 @ X27 @ X26 @ X28))
% 0.19/0.50          | ((sk_D) = (X28))
% 0.19/0.50          | ~ (m1_subset_1 @ X28 @ sk_C)
% 0.19/0.50          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.50           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X26 @ sk_B)
% 0.19/0.50          | ((sk_E) != (k4_tarski @ (k4_tarski @ X27 @ X26) @ X28))
% 0.19/0.50          | ((sk_D) = (X28))
% 0.19/0.50          | ~ (m1_subset_1 @ X28 @ sk_C)
% 0.19/0.50          | ~ (m1_subset_1 @ X27 @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ X2 @ sk_C)
% 0.19/0.50          | ((sk_D) = (X2))
% 0.19/0.50          | ((sk_E)
% 0.19/0.50              != (k4_tarski @ 
% 0.19/0.50                  (k4_tarski @ X1 @ (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50                  X2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['43', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E) != (sk_E))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.50          | ~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['32', '47'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.50          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.50          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.19/0.50          | ~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.19/0.50      inference('sup-', [status(thm)], ['20', '49'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.50          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X21 @ X22 @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | (m1_subset_1 @ (sk_H @ X24 @ X25 @ X23 @ X22 @ X21) @ X23))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_mcart_1])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.50         (((X21) = (k1_xboole_0))
% 0.19/0.50          | ((X22) = (k1_xboole_0))
% 0.19/0.50          | ((X23) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X24 @ 
% 0.19/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22) @ X23))
% 0.19/0.50          | ((X25) = (k5_mcart_1 @ X21 @ X22 @ X23 @ X24))
% 0.19/0.50          | (m1_subset_1 @ (sk_H @ X24 @ X25 @ X23 @ X22 @ X21) @ X23))),
% 0.19/0.50      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.50          | ((X0) = (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['52', '55'])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.19/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.50  thf('58', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['56', '57'])).
% 0.19/0.50  thf('59', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('61', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('62', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((m1_subset_1 @ (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['58', '59', '60', '61'])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_D) = (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))),
% 0.19/0.50      inference('clc', [status(thm)], ['51', '62'])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E)
% 0.19/0.50            = (k4_tarski @ 
% 0.19/0.50               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50               (sk_H @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['28', '29', '30', '31'])).
% 0.19/0.50  thf('65', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E)
% 0.19/0.50            = (k4_tarski @ 
% 0.19/0.50               (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50               sk_D))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['63', '64'])).
% 0.19/0.50  thf('66', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_E)
% 0.19/0.50              = (k4_tarski @ 
% 0.19/0.50                 (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                  (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50                 sk_D)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['65'])).
% 0.19/0.50  thf('67', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('68', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((sk_E)
% 0.19/0.50              = (k4_tarski @ 
% 0.19/0.50                 (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                  (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50                 sk_D)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['65'])).
% 0.19/0.50  thf(t68_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50            ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50            ( ?[E:$i,F:$i,G:$i]:
% 0.19/0.50              ( ( ~( ( ( k5_mcart_1 @ A @ B @ C @ D ) = ( E ) ) & 
% 0.19/0.50                     ( ( k6_mcart_1 @ A @ B @ C @ D ) = ( F ) ) & 
% 0.19/0.50                     ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( G ) ) ) ) & 
% 0.19/0.50                ( ( D ) = ( k3_mcart_1 @ E @ F @ G ) ) ) ) ) ) ))).
% 0.19/0.50  thf('69', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.50         (((X14) = (k1_xboole_0))
% 0.19/0.50          | ((X15) = (k1_xboole_0))
% 0.19/0.50          | ((X16) = (k1_xboole_0))
% 0.19/0.50          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X16 @ X15 @ X14))
% 0.19/0.50          | ((k7_mcart_1 @ X16 @ X15 @ X14 @ X17) = (X20))
% 0.19/0.50          | ((X17) != (k3_mcart_1 @ X18 @ X19 @ X20)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t68_mcart_1])).
% 0.19/0.50  thf('70', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.50         (((k7_mcart_1 @ X16 @ X15 @ X14 @ (k3_mcart_1 @ X18 @ X19 @ X20))
% 0.19/0.50            = (X20))
% 0.19/0.50          | ~ (m1_subset_1 @ (k3_mcart_1 @ X18 @ X19 @ X20) @ 
% 0.19/0.50               (k3_zfmisc_1 @ X16 @ X15 @ X14))
% 0.19/0.50          | ((X16) = (k1_xboole_0))
% 0.19/0.50          | ((X15) = (k1_xboole_0))
% 0.19/0.50          | ((X14) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['69'])).
% 0.19/0.50  thf('71', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.50           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.50  thf('72', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((k3_mcart_1 @ X0 @ X1 @ X2)
% 0.19/0.50           = (k4_tarski @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.19/0.50  thf('73', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('74', plain,
% 0.19/0.50      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.50         (((k7_mcart_1 @ X16 @ X15 @ X14 @ 
% 0.19/0.50            (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20)) = (X20))
% 0.19/0.50          | ~ (m1_subset_1 @ (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20) @ 
% 0.19/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X15) @ X14))
% 0.19/0.50          | ((X16) = (k1_xboole_0))
% 0.19/0.50          | ((X15) = (k1_xboole_0))
% 0.19/0.50          | ((X14) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.19/0.50  thf('75', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1) @ X0))
% 0.19/0.50          | ((X3) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((X0) = (k1_xboole_0))
% 0.19/0.50          | ((X1) = (k1_xboole_0))
% 0.19/0.50          | ((X2) = (k1_xboole_0))
% 0.19/0.50          | ((k7_mcart_1 @ X2 @ X1 @ X0 @ 
% 0.19/0.50              (k4_tarski @ 
% 0.19/0.50               (k4_tarski @ (sk_F @ sk_E @ X3 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50                (sk_G @ sk_E @ X3 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50               sk_D))
% 0.19/0.50              = (sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['68', '74'])).
% 0.19/0.50  thf('76', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ 
% 0.19/0.50            (k4_tarski @ 
% 0.19/0.50             (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50              (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50             sk_D))
% 0.19/0.50            = (sk_D))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0))
% 0.19/0.50          | ((sk_B) = (k1_xboole_0))
% 0.19/0.50          | ((sk_C) = (k1_xboole_0))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('sup-', [status(thm)], ['67', '75'])).
% 0.19/0.50  thf('77', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('78', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('79', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('80', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ 
% 0.19/0.50            (k4_tarski @ 
% 0.19/0.50             (k4_tarski @ (sk_F @ sk_E @ X0 @ sk_C @ sk_B @ sk_A) @ 
% 0.19/0.50              (sk_G @ sk_E @ X0 @ sk_C @ sk_B @ sk_A)) @ 
% 0.19/0.50             sk_D))
% 0.19/0.50            = (sk_D))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['76', '77', '78', '79'])).
% 0.19/0.50  thf('81', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.19/0.50      inference('sup+', [status(thm)], ['66', '80'])).
% 0.19/0.50  thf('82', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50          | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['81'])).
% 0.19/0.50  thf('83', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf(t51_mcart_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.50          ( ~( ![D:$i]:
% 0.19/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.19/0.50                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.50                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.19/0.50                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.19/0.50  thf('84', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         (((X10) = (k1_xboole_0))
% 0.19/0.50          | ((X11) = (k1_xboole_0))
% 0.19/0.50          | ((X13) != (k5_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.19/0.50          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X10 @ X11 @ X12))
% 0.19/0.50          | ((X12) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t51_mcart_1])).
% 0.19/0.50  thf('85', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('86', plain,
% 0.19/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.50         (((X10) = (k1_xboole_0))
% 0.19/0.50          | ((X11) = (k1_xboole_0))
% 0.19/0.50          | ((X13) != (k5_mcart_1 @ X10 @ X11 @ X12 @ X13))
% 0.19/0.50          | ~ (m1_subset_1 @ X13 @ 
% 0.19/0.50               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))
% 0.19/0.50          | ((X12) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.19/0.50  thf('87', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | ((sk_E) != (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))
% 0.19/0.50        | ((sk_B) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['83', '86'])).
% 0.19/0.50  thf('88', plain,
% 0.19/0.50      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.19/0.50         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.19/0.50  thf('89', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | ((sk_E) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.19/0.50        | ((sk_B) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['87', '88'])).
% 0.19/0.50  thf('90', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('92', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('93', plain, (((sk_E) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['89', '90', '91', '92'])).
% 0.19/0.50  thf('94', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_E) != (X0))
% 0.19/0.50          | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['82', '93'])).
% 0.19/0.50  thf('95', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_E @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ sk_C))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '1'])).
% 0.19/0.50  thf('96', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (((X6) = (k1_xboole_0))
% 0.19/0.50          | ((X7) = (k1_xboole_0))
% 0.19/0.50          | ((k7_mcart_1 @ X6 @ X7 @ X9 @ X8) = (k2_mcart_1 @ X8))
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k3_zfmisc_1 @ X6 @ X7 @ X9))
% 0.19/0.50          | ((X9) = (k1_xboole_0)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.19/0.50  thf('97', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.19/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.19/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.19/0.50  thf('98', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.50         (((X6) = (k1_xboole_0))
% 0.19/0.50          | ((X7) = (k1_xboole_0))
% 0.19/0.50          | ((k7_mcart_1 @ X6 @ X7 @ X9 @ X8) = (k2_mcart_1 @ X8))
% 0.19/0.50          | ~ (m1_subset_1 @ X8 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X9))
% 0.19/0.50          | ((X9) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['96', '97'])).
% 0.19/0.50  thf('99', plain,
% 0.19/0.50      ((((sk_C) = (k1_xboole_0))
% 0.19/0.50        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.19/0.50        | ((sk_B) = (k1_xboole_0))
% 0.19/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['95', '98'])).
% 0.19/0.50  thf('100', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('101', plain, (((sk_B) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('102', plain, (((sk_C) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('103', plain,
% 0.19/0.50      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['99', '100', '101', '102'])).
% 0.19/0.50  thf('104', plain,
% 0.19/0.50      (![X0 : $i]: (((sk_E) != (X0)) | ((k2_mcart_1 @ sk_E) = (sk_D)))),
% 0.19/0.50      inference('demod', [status(thm)], ['94', '103'])).
% 0.19/0.50  thf('105', plain, (((k2_mcart_1 @ sk_E) = (sk_D))),
% 0.19/0.50      inference('simplify', [status(thm)], ['104'])).
% 0.19/0.50  thf('106', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('107', plain,
% 0.19/0.50      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['99', '100', '101', '102'])).
% 0.19/0.50  thf('108', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 0.19/0.50      inference('demod', [status(thm)], ['106', '107'])).
% 0.19/0.50  thf('109', plain, ($false),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['105', '108'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
