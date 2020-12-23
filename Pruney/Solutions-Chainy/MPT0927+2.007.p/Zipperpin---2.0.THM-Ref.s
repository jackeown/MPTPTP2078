%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7l807wFRLR

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:20 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 552 expanded)
%              Number of leaves         :   30 ( 184 expanded)
%              Depth                    :   33
%              Number of atoms          : 1857 (10240 expanded)
%              Number of equality atoms :  158 ( 246 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_I_type,type,(
    sk_I: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t87_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
     => ! [F: $i] :
          ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
         => ! [G: $i] :
              ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                     => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                       => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                          & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                          & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                          & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
       => ! [F: $i] :
            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) )
                   => ! [I: $i] :
                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
                       => ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) )
                         => ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E )
                            & ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F )
                            & ( r2_hidden @ ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G )
                            & ( r2_hidden @ ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('18',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X6 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
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

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X16 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('33',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['14','15'])).

thf('34',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['17','20'])).

thf('35',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('36',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16 )
        = ( k2_mcart_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('38',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['30'])).

thf('40',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('42',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_C = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_C = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['34','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['33','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_E )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['32','67'])).

thf('69',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('70',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['14','15'])).

thf('71',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['17','20'])).

thf('72',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('73',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('75',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['30'])).

thf('77',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['17','20'])).

thf('79',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_C = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( sk_C = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['72','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('86',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['71','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['70','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('96',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('98',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_E )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G ),
    inference('sup-',[status(thm)],['69','98'])).

thf('100',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('101',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['14','15'])).

thf('102',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['17','20'])).

thf('103',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['22','25'])).

thf('104',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( X14 = k1_xboole_0 )
      | ( X15 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X16 ) ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17 ) )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('106',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['30'])).

thf('108',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['14','15'])).

thf('110',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_C = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,
    ( ! [X0: $i] :
        ( ( sk_C = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['103','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['102','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['101','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('127',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('129',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_E )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F ),
    inference('sup-',[status(thm)],['100','129'])).

thf('131',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['30'])).

thf('132',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['68','99','130','131'])).

thf('133',plain,(
    ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['31','132'])).

thf('134',plain,
    ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','133'])).

thf('135',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('136',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_H ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_G ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['16','150'])).

thf('152',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('153',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_E ) ),
    inference(demod,[status(thm)],['13','151','152'])).

thf('154',plain,(
    $false ),
    inference('sup-',[status(thm)],['10','153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7l807wFRLR
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 161 iterations in 0.092s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(sk_I_type, type, sk_I: $i).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.56  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.36/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.36/0.56  thf(sk_H_type, type, sk_H: $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.36/0.56  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.36/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.36/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.36/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.56  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.56  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.56  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.36/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(t87_mcart_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.56       ( ![F:$i]:
% 0.36/0.56         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.36/0.56           ( ![G:$i]:
% 0.36/0.56             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.36/0.56               ( ![H:$i]:
% 0.36/0.56                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.36/0.56                   ( ![I:$i]:
% 0.36/0.56                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.36/0.56                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.36/0.56                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.36/0.56                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.36/0.56                           ( r2_hidden @
% 0.36/0.56                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.36/0.56                           ( r2_hidden @
% 0.36/0.56                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.36/0.56        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.56          ( ![F:$i]:
% 0.36/0.56            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.36/0.56              ( ![G:$i]:
% 0.36/0.56                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.36/0.56                  ( ![H:$i]:
% 0.36/0.56                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.36/0.56                      ( ![I:$i]:
% 0.36/0.56                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.36/0.56                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.36/0.56                            ( ( r2_hidden @
% 0.36/0.56                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.36/0.56                              ( r2_hidden @
% 0.36/0.56                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.36/0.56                              ( r2_hidden @
% 0.36/0.56                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.36/0.56                              ( r2_hidden @
% 0.36/0.56                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(d4_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.36/0.56       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf(t10_mcart_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.36/0.56       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.36/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((r2_hidden @ (k1_mcart_1 @ X10) @ X11)
% 0.36/0.56          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.56          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.36/0.56  thf(d3_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.36/0.56       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.36/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((r2_hidden @ (k1_mcart_1 @ X10) @ X11)
% 0.36/0.56          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.56  thf('7', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.36/0.56          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.36/0.56        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '7'])).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((r2_hidden @ (k1_mcart_1 @ X10) @ X11)
% 0.36/0.56          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('11', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t5_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.36/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | ~ (v1_xboole_0 @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.36/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.36/0.56        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['4', '7'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((r2_hidden @ (k2_mcart_1 @ X10) @ X12)
% 0.36/0.56          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.36/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('17', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.56         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.36/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((r2_hidden @ (k2_mcart_1 @ X10) @ X12)
% 0.36/0.56          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.56  thf('20', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.36/0.56          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.56  thf('21', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.36/0.56         ((k4_zfmisc_1 @ X6 @ X7 @ X8 @ X9)
% 0.36/0.56           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X6 @ X7 @ X8) @ X9))),
% 0.36/0.56      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.36/0.56         ((r2_hidden @ (k2_mcart_1 @ X10) @ X12)
% 0.36/0.56          | ~ (r2_hidden @ X10 @ (k2_zfmisc_1 @ X11 @ X12)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.36/0.56          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.36/0.56  thf('26', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t61_mcart_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56          ( ~( ![E:$i]:
% 0.36/0.56               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.36/0.56                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.36/0.56                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.36/0.56                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.36/0.56                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.36/0.56                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.36/0.56                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.36/0.56                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         (((X13) = (k1_xboole_0))
% 0.36/0.56          | ((X14) = (k1_xboole_0))
% 0.36/0.56          | ((X15) = (k1_xboole_0))
% 0.36/0.56          | ((k8_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16)
% 0.36/0.56              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X16))))
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17))
% 0.36/0.56          | ((X17) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      ((((sk_D) = (k1_xboole_0))
% 0.36/0.56        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.36/0.56            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E)
% 0.36/0.56        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F)
% 0.36/0.56        | ~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56             sk_G)
% 0.36/0.56        | ~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56             sk_H))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_E)))),
% 0.36/0.56      inference('split', [status(esa)], ['30'])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('33', plain,
% 0.36/0.56      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.36/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('34', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf('35', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.56  thf('36', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         (((X13) = (k1_xboole_0))
% 0.36/0.56          | ((X14) = (k1_xboole_0))
% 0.36/0.56          | ((X15) = (k1_xboole_0))
% 0.36/0.56          | ((k11_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16) = (k2_mcart_1 @ X16))
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17))
% 0.36/0.56          | ((X17) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.36/0.56  thf('38', plain,
% 0.36/0.56      ((((sk_D) = (k1_xboole_0))
% 0.36/0.56        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.36/0.56            = (k2_mcart_1 @ sk_I))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.56  thf('39', plain,
% 0.36/0.56      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_H))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('split', [status(esa)], ['30'])).
% 0.36/0.56  thf('40', plain,
% 0.36/0.56      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.56  thf('41', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.56  thf('42', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.56  thf('43', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('44', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | ~ (v1_xboole_0 @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('45', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('46', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_C) = (k1_xboole_0))
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_H)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['42', '45'])).
% 0.36/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.56  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('48', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((sk_C) = (k1_xboole_0))
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_H)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.36/0.56  thf('49', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['35', '48'])).
% 0.36/0.56  thf('50', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('51', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | ~ (v1_xboole_0 @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('52', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.56  thf('53', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_G)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['49', '52'])).
% 0.36/0.56  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('55', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_G)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.36/0.56  thf('56', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['34', '55'])).
% 0.36/0.56  thf('57', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('58', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | ~ (v1_xboole_0 @ X2)
% 0.36/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.36/0.56  thf('59', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('60', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['56', '59'])).
% 0.36/0.56  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('62', plain,
% 0.36/0.56      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_F)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('demod', [status(thm)], ['60', '61'])).
% 0.36/0.56  thf('63', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['33', '62'])).
% 0.36/0.56  thf('64', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.36/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf('65', plain,
% 0.36/0.56      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.36/0.56  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('67', plain,
% 0.36/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_E))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_H)))),
% 0.36/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.36/0.56  thf('68', plain,
% 0.36/0.56      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 0.36/0.56      inference('sup-', [status(thm)], ['32', '67'])).
% 0.36/0.56  thf('69', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('70', plain,
% 0.36/0.56      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.36/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('71', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf('72', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.56  thf('73', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('74', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         (((X13) = (k1_xboole_0))
% 0.36/0.56          | ((X14) = (k1_xboole_0))
% 0.36/0.56          | ((X15) = (k1_xboole_0))
% 0.36/0.56          | ((k10_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16)
% 0.36/0.56              = (k2_mcart_1 @ (k1_mcart_1 @ X16)))
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17))
% 0.36/0.56          | ((X17) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.36/0.56  thf('75', plain,
% 0.36/0.56      ((((sk_D) = (k1_xboole_0))
% 0.36/0.56        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.36/0.56            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.56  thf('76', plain,
% 0.36/0.56      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_G))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('split', [status(esa)], ['30'])).
% 0.36/0.56  thf('77', plain,
% 0.36/0.56      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.36/0.56  thf('78', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf('79', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['77', '78'])).
% 0.36/0.56  thf('80', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('81', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_C) = (k1_xboole_0))
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_H)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['79', '80'])).
% 0.36/0.56  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('83', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((sk_C) = (k1_xboole_0))
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_H)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['81', '82'])).
% 0.36/0.56  thf('84', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['72', '83'])).
% 0.36/0.56  thf('85', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.56  thf('86', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_G)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['84', '85'])).
% 0.36/0.56  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('88', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_G)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.36/0.56  thf('89', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['71', '88'])).
% 0.36/0.56  thf('90', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('91', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['89', '90'])).
% 0.36/0.56  thf('92', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('93', plain,
% 0.36/0.56      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_F)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['91', '92'])).
% 0.36/0.56  thf('94', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['70', '93'])).
% 0.36/0.56  thf('95', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.36/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf('96', plain,
% 0.36/0.56      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.36/0.56  thf('97', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('98', plain,
% 0.36/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_E))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_G)))),
% 0.36/0.56      inference('demod', [status(thm)], ['96', '97'])).
% 0.36/0.56  thf('99', plain,
% 0.36/0.56      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['69', '98'])).
% 0.36/0.56  thf('100', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('101', plain,
% 0.36/0.56      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.36/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('102', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '20'])).
% 0.36/0.56  thf('103', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.36/0.56      inference('sup-', [status(thm)], ['22', '25'])).
% 0.36/0.56  thf('104', plain,
% 0.36/0.56      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('105', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.56         (((X13) = (k1_xboole_0))
% 0.36/0.56          | ((X14) = (k1_xboole_0))
% 0.36/0.56          | ((X15) = (k1_xboole_0))
% 0.36/0.56          | ((k9_mcart_1 @ X13 @ X14 @ X15 @ X17 @ X16)
% 0.36/0.56              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X16))))
% 0.36/0.56          | ~ (m1_subset_1 @ X16 @ (k4_zfmisc_1 @ X13 @ X14 @ X15 @ X17))
% 0.36/0.56          | ((X17) = (k1_xboole_0)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.36/0.56  thf('106', plain,
% 0.36/0.56      ((((sk_D) = (k1_xboole_0))
% 0.36/0.56        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I)
% 0.36/0.56            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['104', '105'])).
% 0.36/0.56  thf('107', plain,
% 0.36/0.56      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('split', [status(esa)], ['30'])).
% 0.36/0.56  thf('108', plain,
% 0.36/0.56      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.36/0.56            sk_F)
% 0.36/0.56         | ((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['106', '107'])).
% 0.36/0.56  thf('109', plain,
% 0.36/0.56      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.36/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('110', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))
% 0.36/0.56         | ((sk_D) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('demod', [status(thm)], ['108', '109'])).
% 0.36/0.56  thf('111', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('112', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_C) = (k1_xboole_0))
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_H)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['110', '111'])).
% 0.36/0.56  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('114', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((sk_C) = (k1_xboole_0))
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_H)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('demod', [status(thm)], ['112', '113'])).
% 0.36/0.56  thf('115', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0))
% 0.36/0.56         | ((sk_B) = (k1_xboole_0))
% 0.36/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['103', '114'])).
% 0.36/0.56  thf('116', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.56  thf('117', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_G)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['115', '116'])).
% 0.36/0.56  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('119', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (((sk_B) = (k1_xboole_0))
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_G)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('demod', [status(thm)], ['117', '118'])).
% 0.36/0.56  thf('120', plain,
% 0.36/0.56      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['102', '119'])).
% 0.36/0.56  thf('121', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('122', plain,
% 0.36/0.56      ((![X0 : $i]:
% 0.36/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56           | ((sk_A) = (k1_xboole_0))
% 0.36/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['120', '121'])).
% 0.36/0.56  thf('123', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('124', plain,
% 0.36/0.56      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_F)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('demod', [status(thm)], ['122', '123'])).
% 0.36/0.56  thf('125', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['101', '124'])).
% 0.36/0.56  thf('126', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.36/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.56  thf('127', plain,
% 0.36/0.56      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['125', '126'])).
% 0.36/0.56  thf('128', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('129', plain,
% 0.36/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_E))
% 0.36/0.56         <= (~
% 0.36/0.56             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ 
% 0.36/0.56               sk_F)))),
% 0.36/0.56      inference('demod', [status(thm)], ['127', '128'])).
% 0.36/0.56  thf('130', plain,
% 0.36/0.56      (((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['100', '129'])).
% 0.36/0.56  thf('131', plain,
% 0.36/0.56      (~ ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E)) | 
% 0.36/0.56       ~ ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_F)) | 
% 0.36/0.56       ~
% 0.36/0.56       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_G)) | 
% 0.36/0.56       ~
% 0.36/0.56       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 0.36/0.56      inference('split', [status(esa)], ['30'])).
% 0.36/0.56  thf('132', plain,
% 0.36/0.56      (~ ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['68', '99', '130', '131'])).
% 0.36/0.56  thf('133', plain,
% 0.36/0.56      (~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_I) @ sk_E)),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['31', '132'])).
% 0.36/0.56  thf('134', plain,
% 0.36/0.56      ((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)
% 0.36/0.56        | ((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['29', '133'])).
% 0.36/0.56  thf('135', plain,
% 0.36/0.56      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('136', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0))
% 0.36/0.56        | ((sk_D) = (k1_xboole_0)))),
% 0.36/0.56      inference('demod', [status(thm)], ['134', '135'])).
% 0.36/0.56  thf('137', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_D) | ~ (r2_hidden @ X0 @ sk_H))),
% 0.36/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.56  thf('138', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56          | ((sk_C) = (k1_xboole_0))
% 0.36/0.56          | ((sk_B) = (k1_xboole_0))
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_H))),
% 0.36/0.56      inference('sup-', [status(thm)], ['136', '137'])).
% 0.36/0.56  thf('139', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('140', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((sk_C) = (k1_xboole_0))
% 0.36/0.56          | ((sk_B) = (k1_xboole_0))
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_H))),
% 0.36/0.56      inference('demod', [status(thm)], ['138', '139'])).
% 0.36/0.56  thf('141', plain,
% 0.36/0.56      ((((sk_A) = (k1_xboole_0))
% 0.36/0.56        | ((sk_B) = (k1_xboole_0))
% 0.36/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['26', '140'])).
% 0.36/0.56  thf('142', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.56  thf('143', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56          | ((sk_B) = (k1_xboole_0))
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_G))),
% 0.36/0.56      inference('sup-', [status(thm)], ['141', '142'])).
% 0.36/0.56  thf('144', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('145', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (((sk_B) = (k1_xboole_0))
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_G))),
% 0.36/0.56      inference('demod', [status(thm)], ['143', '144'])).
% 0.36/0.56  thf('146', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['21', '145'])).
% 0.36/0.56  thf('147', plain,
% 0.36/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.56  thf('148', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.56          | ((sk_A) = (k1_xboole_0))
% 0.36/0.56          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.36/0.56      inference('sup-', [status(thm)], ['146', '147'])).
% 0.36/0.56  thf('149', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('150', plain,
% 0.36/0.56      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.36/0.56      inference('demod', [status(thm)], ['148', '149'])).
% 0.36/0.56  thf('151', plain, (((sk_A) = (k1_xboole_0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['16', '150'])).
% 0.36/0.56  thf('152', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.56  thf('153', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_E)),
% 0.36/0.56      inference('demod', [status(thm)], ['13', '151', '152'])).
% 0.36/0.56  thf('154', plain, ($false), inference('sup-', [status(thm)], ['10', '153'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
