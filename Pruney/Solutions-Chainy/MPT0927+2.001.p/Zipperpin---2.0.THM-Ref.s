%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTiP3ytkAl

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:19 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  224 ( 817 expanded)
%              Number of leaves         :   32 ( 273 expanded)
%              Depth                    :   31
%              Number of atoms          : 2060 (11681 expanded)
%              Number of equality atoms :  166 ( 250 expanded)
%              Maximal formula depth    :   27 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(sk_I_type,type,(
    sk_I: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

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

thf('13',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
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

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('22',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('28',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X4 ) @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('36',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_F ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference(demod,[status(thm)],['25','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('40',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ sk_I ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['23'])).

thf('42',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r2_hidden @ sk_I @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('45',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X4 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X8 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('56',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('57',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['70','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('84',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ ( k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('94',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,
    ( ( v1_xboole_0 @ sk_E )
   <= ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('98',plain,(
    r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_I ) @ ( k3_zfmisc_1 @ sk_E @ sk_F @ sk_G ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('100',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('101',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('106',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(split,[status(esa)],['23'])).

thf('108',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ sk_G )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('111',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('113',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('115',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('117',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('119',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('121',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('123',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('125',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('127',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('129',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('131',plain,
    ( ( v1_xboole_0 @ sk_E )
   <= ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('133',plain,(
    r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('135',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('136',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_I @ ( k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('139',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(split,[status(esa)],['23'])).

thf('141',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_I ) ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['136','141'])).

thf('143',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('144',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('146',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_H ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('148',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('150',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('152',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_G ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('154',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('156',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('158',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('160',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('162',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('164',plain,
    ( ( v1_xboole_0 @ sk_E )
   <= ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('166',plain,(
    r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,
    ( ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F )
    | ~ ( r2_hidden @ ( k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_E )
    | ~ ( r2_hidden @ ( k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_G )
    | ~ ( r2_hidden @ ( k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_H ) ),
    inference(split,[status(esa)],['23'])).

thf('168',plain,(
    ~ ( r2_hidden @ ( k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['98','133','166','167'])).

thf('169',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['37','168'])).

thf('170',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('171',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('173',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_H ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    ~ ( v1_xboole_0 @ sk_H ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('175',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('177',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('179',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_G ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_G ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('181',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('183',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('185',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('187',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('189',plain,(
    v1_xboole_0 @ sk_E ),
    inference(demod,[status(thm)],['19','187','188'])).

thf('190',plain,(
    $false ),
    inference(demod,[status(thm)],['16','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hTiP3ytkAl
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:07:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 173 iterations in 0.070s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.37/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.37/0.54  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.54  thf(sk_E_type, type, sk_E: $i).
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.54  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.54  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.37/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.54  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.37/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(sk_G_type, type, sk_G: $i).
% 0.37/0.54  thf(sk_F_type, type, sk_F: $i).
% 0.37/0.54  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.37/0.54  thf(sk_H_type, type, sk_H: $i).
% 0.37/0.54  thf(sk_I_type, type, sk_I: $i).
% 0.37/0.54  thf(d1_xboole_0, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf(t10_mcart_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.37/0.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.37/0.54         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.37/0.54          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf(d3_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.37/0.54       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.54         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.37/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf('7', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.54          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.54  thf(d4_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.37/0.54       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.54         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.37/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.54          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.37/0.54      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ X2)
% 0.37/0.54          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['8', '11'])).
% 0.37/0.54  thf(t87_mcart_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.54     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.54       ( ![F:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.37/0.54           ( ![G:$i]:
% 0.37/0.54             ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.37/0.54               ( ![H:$i]:
% 0.37/0.54                 ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.37/0.54                   ( ![I:$i]:
% 0.37/0.54                     ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.37/0.54                       ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.37/0.54                         ( ( r2_hidden @ ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.37/0.54                           ( r2_hidden @ ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.37/0.54                           ( r2_hidden @
% 0.37/0.54                             ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.37/0.54                           ( r2_hidden @
% 0.37/0.54                             ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.37/0.54        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.54          ( ![F:$i]:
% 0.37/0.54            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) ) =>
% 0.37/0.54              ( ![G:$i]:
% 0.37/0.54                ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ C ) ) =>
% 0.37/0.54                  ( ![H:$i]:
% 0.37/0.54                    ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ D ) ) =>
% 0.37/0.54                      ( ![I:$i]:
% 0.37/0.54                        ( ( m1_subset_1 @ I @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.37/0.54                          ( ( r2_hidden @ I @ ( k4_zfmisc_1 @ E @ F @ G @ H ) ) =>
% 0.37/0.54                            ( ( r2_hidden @
% 0.37/0.54                                ( k8_mcart_1 @ A @ B @ C @ D @ I ) @ E ) & 
% 0.37/0.54                              ( r2_hidden @
% 0.37/0.54                                ( k9_mcart_1 @ A @ B @ C @ D @ I ) @ F ) & 
% 0.37/0.54                              ( r2_hidden @
% 0.37/0.54                                ( k10_mcart_1 @ A @ B @ C @ D @ I ) @ G ) & 
% 0.37/0.54                              ( r2_hidden @
% 0.37/0.54                                ( k11_mcart_1 @ A @ B @ C @ D @ I ) @ H ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t87_mcart_1])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('16', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.37/0.54      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.54  thf('17', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(cc1_subset_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_xboole_0 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.54          | (v1_xboole_0 @ X3)
% 0.37/0.54          | ~ (v1_xboole_0 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.54  thf('19', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_E))),
% 0.37/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf(t61_mcart_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.37/0.54          ( ~( ![E:$i]:
% 0.37/0.54               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.37/0.54                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.37/0.54                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.37/0.54                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.37/0.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.37/0.54                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.37/0.54                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.37/0.54                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         (((X15) = (k1_xboole_0))
% 0.37/0.54          | ((X16) = (k1_xboole_0))
% 0.37/0.54          | ((X17) = (k1_xboole_0))
% 0.37/0.54          | ((k9_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18)
% 0.37/0.54              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X18))))
% 0.37/0.54          | ~ (m1_subset_1 @ X18 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19))
% 0.37/0.54          | ((X19) = (k1_xboole_0)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      ((((sk_D) = (k1_xboole_0))
% 0.37/0.54        | ((k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 0.37/0.54            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.37/0.54        | ((sk_C) = (k1_xboole_0))
% 0.37/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E)
% 0.37/0.54        | ~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54             sk_F)
% 0.37/0.54        | ~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54             sk_G)
% 0.37/0.54        | ~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54             sk_H))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      ((~ (r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_F))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54               sk_F)))),
% 0.37/0.54      inference('split', [status(esa)], ['23'])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.37/0.54            sk_F)
% 0.37/0.54         | ((sk_A) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_C) = (k1_xboole_0))
% 0.37/0.54         | ((sk_D) = (k1_xboole_0))))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54               sk_F)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['22', '24'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.54         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.37/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.54          | (r2_hidden @ (k1_mcart_1 @ X4) @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.37/0.54      inference('sup-', [status(thm)], ['26', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.54         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.37/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.54          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.37/0.54        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.37/0.54      inference('sup-', [status(thm)], ['30', '33'])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_F)),
% 0.37/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (((((sk_A) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_C) = (k1_xboole_0))
% 0.37/0.54         | ((sk_D) = (k1_xboole_0))))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54               sk_F)))),
% 0.37/0.54      inference('demod', [status(thm)], ['25', '36'])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.54         (((X15) = (k1_xboole_0))
% 0.37/0.54          | ((X16) = (k1_xboole_0))
% 0.37/0.54          | ((X17) = (k1_xboole_0))
% 0.37/0.54          | ((k11_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18) = (k2_mcart_1 @ X18))
% 0.37/0.54          | ~ (m1_subset_1 @ X18 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19))
% 0.37/0.54          | ((X19) = (k1_xboole_0)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      ((((sk_D) = (k1_xboole_0))
% 0.37/0.54        | ((k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 0.37/0.54            = (k2_mcart_1 @ sk_I))
% 0.37/0.54        | ((sk_C) = (k1_xboole_0))
% 0.37/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.54  thf('41', plain,
% 0.37/0.54      ((~ (r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.54           sk_H))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('split', [status(esa)], ['23'])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (((~ (r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)
% 0.37/0.54         | ((sk_A) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_C) = (k1_xboole_0))
% 0.37/0.54         | ((sk_D) = (k1_xboole_0))))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      ((r2_hidden @ sk_I @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.54         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.37/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X4 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.54          | (r2_hidden @ (k2_mcart_1 @ X4) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.54  thf('47', plain, ((r2_hidden @ (k2_mcart_1 @ sk_I) @ sk_H)),
% 0.37/0.54      inference('sup-', [status(thm)], ['43', '46'])).
% 0.37/0.54  thf('48', plain,
% 0.37/0.54      (((((sk_A) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_C) = (k1_xboole_0))
% 0.37/0.54         | ((sk_D) = (k1_xboole_0))))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('demod', [status(thm)], ['42', '47'])).
% 0.37/0.54  thf('49', plain, ((m1_subset_1 @ sk_H @ (k1_zfmisc_1 @ sk_D))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('50', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.54          | (v1_xboole_0 @ X3)
% 0.37/0.54          | ~ (v1_xboole_0 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.54  thf('51', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_H))),
% 0.37/0.54      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54         | ((sk_C) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_A) = (k1_xboole_0))
% 0.37/0.54         | (v1_xboole_0 @ sk_H)))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['48', '51'])).
% 0.37/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.54  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      (((((sk_C) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_A) = (k1_xboole_0))
% 0.37/0.54         | (v1_xboole_0 @ sk_H)))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.54  thf('55', plain,
% 0.37/0.54      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.37/0.54         ((k4_zfmisc_1 @ X8 @ X9 @ X10 @ X11)
% 0.37/0.54           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X8 @ X9 @ X10) @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.37/0.54  thf('56', plain,
% 0.37/0.54      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf('57', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.54         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.37/0.54          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.54  thf('58', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.37/0.54          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.54  thf('60', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.54  thf('61', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.54          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['55', '60'])).
% 0.37/0.54  thf('62', plain,
% 0.37/0.54      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('63', plain, (~ (v1_xboole_0 @ sk_H)),
% 0.37/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.54  thf('64', plain,
% 0.37/0.54      (((((sk_A) = (k1_xboole_0))
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_C) = (k1_xboole_0))))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['54', '63'])).
% 0.37/0.54  thf('65', plain, ((m1_subset_1 @ sk_G @ (k1_zfmisc_1 @ sk_C))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('66', plain,
% 0.37/0.54      (![X3 : $i, X4 : $i]:
% 0.37/0.54         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.54          | (v1_xboole_0 @ X3)
% 0.37/0.54          | ~ (v1_xboole_0 @ X4))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.54  thf('67', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_G))),
% 0.37/0.54      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.54  thf('68', plain,
% 0.37/0.54      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_A) = (k1_xboole_0))
% 0.37/0.54         | (v1_xboole_0 @ sk_G)))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['64', '67'])).
% 0.37/0.54  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('70', plain,
% 0.37/0.54      (((((sk_B_1) = (k1_xboole_0))
% 0.37/0.54         | ((sk_A) = (k1_xboole_0))
% 0.37/0.54         | (v1_xboole_0 @ sk_G)))
% 0.37/0.54         <= (~
% 0.37/0.54             ((r2_hidden @ 
% 0.37/0.54               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.37/0.54  thf('71', plain,
% 0.37/0.54      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.54         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.37/0.54           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.54  thf('72', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.54  thf('73', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['71', '72'])).
% 0.37/0.55  thf('74', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.55          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('75', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ X0)
% 0.37/0.55          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.37/0.55  thf('76', plain,
% 0.37/0.55      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('77', plain, (~ (v1_xboole_0 @ sk_G)),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('78', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['70', '77'])).
% 0.37/0.55  thf('79', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_B_1))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('80', plain,
% 0.37/0.55      (![X3 : $i, X4 : $i]:
% 0.37/0.55         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.37/0.55          | (v1_xboole_0 @ X3)
% 0.37/0.55          | ~ (v1_xboole_0 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.37/0.55  thf('81', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.55  thf('82', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_F)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['78', '81'])).
% 0.37/0.55  thf('83', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('84', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_F)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.55      inference('demod', [status(thm)], ['82', '83'])).
% 0.37/0.55  thf('85', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.55  thf('86', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.55          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['5', '6'])).
% 0.37/0.55  thf('87', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['85', '86'])).
% 0.37/0.55  thf('88', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         ((v1_xboole_0 @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.37/0.55          | ~ (v1_xboole_0 @ (k3_zfmisc_1 @ X3 @ X2 @ X1)))),
% 0.37/0.55      inference('sup+', [status(thm)], ['9', '10'])).
% 0.37/0.55  thf('89', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ X1)
% 0.37/0.55          | (v1_xboole_0 @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ X3)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.37/0.55  thf('90', plain,
% 0.37/0.55      (~ (v1_xboole_0 @ (k4_zfmisc_1 @ sk_E @ sk_F @ sk_G @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.37/0.55  thf('91', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.55  thf('92', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['84', '91'])).
% 0.37/0.55  thf('93', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('94', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_E)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['92', '93'])).
% 0.37/0.55  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('96', plain,
% 0.37/0.55      (((v1_xboole_0 @ sk_E))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H)))),
% 0.37/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.37/0.55  thf('97', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.55  thf('98', plain,
% 0.37/0.55      (((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['96', '97'])).
% 0.37/0.55  thf('99', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ sk_I) @ (k3_zfmisc_1 @ sk_E @ sk_F @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['26', '29'])).
% 0.37/0.55  thf('100', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.37/0.55         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.37/0.55           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.37/0.55      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.37/0.55  thf('101', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.37/0.55          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('102', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.37/0.55         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.37/0.55          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['100', '101'])).
% 0.37/0.55  thf('103', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)),
% 0.37/0.55      inference('sup-', [status(thm)], ['99', '102'])).
% 0.37/0.55  thf('104', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('105', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         (((X15) = (k1_xboole_0))
% 0.37/0.55          | ((X16) = (k1_xboole_0))
% 0.37/0.55          | ((X17) = (k1_xboole_0))
% 0.37/0.55          | ((k10_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18)
% 0.37/0.55              = (k2_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19))
% 0.37/0.55          | ((X19) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.37/0.55  thf('106', plain,
% 0.37/0.55      ((((sk_D) = (k1_xboole_0))
% 0.37/0.55        | ((k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 0.37/0.55            = (k2_mcart_1 @ (k1_mcart_1 @ sk_I)))
% 0.37/0.55        | ((sk_C) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['104', '105'])).
% 0.37/0.55  thf('107', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55           sk_G))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('split', [status(esa)], ['23'])).
% 0.37/0.55  thf('108', plain,
% 0.37/0.55      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_I)) @ sk_G)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.37/0.55  thf('109', plain,
% 0.37/0.55      (((((sk_D) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['103', '108'])).
% 0.37/0.55  thf('110', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('111', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_H)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['109', '110'])).
% 0.37/0.55  thf('112', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('113', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_H)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('demod', [status(thm)], ['111', '112'])).
% 0.37/0.55  thf('114', plain, (~ (v1_xboole_0 @ sk_H)),
% 0.37/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('115', plain,
% 0.37/0.55      (((((sk_C) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.37/0.55  thf('116', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('117', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_G)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['115', '116'])).
% 0.37/0.55  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('119', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_G)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('demod', [status(thm)], ['117', '118'])).
% 0.37/0.55  thf('120', plain, (~ (v1_xboole_0 @ sk_G)),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('121', plain,
% 0.37/0.55      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('clc', [status(thm)], ['119', '120'])).
% 0.37/0.55  thf('122', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.55  thf('123', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_F)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['121', '122'])).
% 0.37/0.55  thf('124', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('125', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_F)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('demod', [status(thm)], ['123', '124'])).
% 0.37/0.55  thf('126', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.55  thf('127', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('clc', [status(thm)], ['125', '126'])).
% 0.37/0.55  thf('128', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('129', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_E)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['127', '128'])).
% 0.37/0.55  thf('130', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('131', plain,
% 0.37/0.55      (((v1_xboole_0 @ sk_E))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ 
% 0.37/0.55               (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)))),
% 0.37/0.55      inference('demod', [status(thm)], ['129', '130'])).
% 0.37/0.55  thf('132', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.55  thf('133', plain,
% 0.37/0.55      (((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['131', '132'])).
% 0.37/0.55  thf('134', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I)) @ 
% 0.37/0.55        (k2_zfmisc_1 @ sk_E @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['30', '33'])).
% 0.37/0.55  thf('135', plain,
% 0.37/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.55         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.37/0.55          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.37/0.55  thf('136', plain,
% 0.37/0.55      ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['134', '135'])).
% 0.37/0.55  thf('137', plain,
% 0.37/0.55      ((m1_subset_1 @ sk_I @ (k4_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('138', plain,
% 0.37/0.55      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.55         (((X15) = (k1_xboole_0))
% 0.37/0.55          | ((X16) = (k1_xboole_0))
% 0.37/0.55          | ((X17) = (k1_xboole_0))
% 0.37/0.55          | ((k8_mcart_1 @ X15 @ X16 @ X17 @ X19 @ X18)
% 0.37/0.55              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X18))))
% 0.37/0.55          | ~ (m1_subset_1 @ X18 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X19))
% 0.37/0.55          | ((X19) = (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.37/0.55  thf('139', plain,
% 0.37/0.55      ((((sk_D) = (k1_xboole_0))
% 0.37/0.55        | ((k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I)
% 0.37/0.55            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))))
% 0.37/0.55        | ((sk_C) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['137', '138'])).
% 0.37/0.55  thf('140', plain,
% 0.37/0.55      ((~ (r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('split', [status(esa)], ['23'])).
% 0.37/0.55  thf('141', plain,
% 0.37/0.55      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_I))) @ 
% 0.37/0.55            sk_E)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | ((sk_D) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['139', '140'])).
% 0.37/0.55  thf('142', plain,
% 0.37/0.55      (((((sk_D) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['136', '141'])).
% 0.37/0.55  thf('143', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('144', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_H)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['142', '143'])).
% 0.37/0.55  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('146', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_C) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_H)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('demod', [status(thm)], ['144', '145'])).
% 0.37/0.55  thf('147', plain, (~ (v1_xboole_0 @ sk_H)),
% 0.37/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('148', plain,
% 0.37/0.55      (((((sk_C) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['146', '147'])).
% 0.37/0.55  thf('149', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('150', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_G)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['148', '149'])).
% 0.37/0.55  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('152', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0))
% 0.37/0.55         | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_G)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('demod', [status(thm)], ['150', '151'])).
% 0.37/0.55  thf('153', plain, (~ (v1_xboole_0 @ sk_G)),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('154', plain,
% 0.37/0.55      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('clc', [status(thm)], ['152', '153'])).
% 0.37/0.55  thf('155', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.55  thf('156', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55         | ((sk_A) = (k1_xboole_0))
% 0.37/0.55         | (v1_xboole_0 @ sk_F)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['154', '155'])).
% 0.37/0.55  thf('157', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('158', plain,
% 0.37/0.55      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_F)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('demod', [status(thm)], ['156', '157'])).
% 0.37/0.55  thf('159', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.55  thf('160', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('clc', [status(thm)], ['158', '159'])).
% 0.37/0.55  thf('161', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.55  thf('162', plain,
% 0.37/0.55      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_E)))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['160', '161'])).
% 0.37/0.55  thf('163', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('164', plain,
% 0.37/0.55      (((v1_xboole_0 @ sk_E))
% 0.37/0.55         <= (~
% 0.37/0.55             ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ 
% 0.37/0.55               sk_E)))),
% 0.37/0.55      inference('demod', [status(thm)], ['162', '163'])).
% 0.37/0.55  thf('165', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '15'])).
% 0.37/0.55  thf('166', plain,
% 0.37/0.55      (((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E))),
% 0.37/0.55      inference('sup-', [status(thm)], ['164', '165'])).
% 0.37/0.55  thf('167', plain,
% 0.37/0.55      (~
% 0.37/0.55       ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_F)) | 
% 0.37/0.55       ~
% 0.37/0.55       ((r2_hidden @ (k8_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_E)) | 
% 0.37/0.55       ~
% 0.37/0.55       ((r2_hidden @ (k10_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_G)) | 
% 0.37/0.55       ~
% 0.37/0.55       ((r2_hidden @ (k11_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_H))),
% 0.37/0.55      inference('split', [status(esa)], ['23'])).
% 0.37/0.55  thf('168', plain,
% 0.37/0.55      (~
% 0.37/0.55       ((r2_hidden @ (k9_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_I) @ sk_F))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['98', '133', '166', '167'])).
% 0.37/0.55  thf('169', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C) = (k1_xboole_0))
% 0.37/0.55        | ((sk_D) = (k1_xboole_0)))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['37', '168'])).
% 0.37/0.55  thf('170', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('171', plain,
% 0.37/0.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55        | ((sk_C) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | (v1_xboole_0 @ sk_H))),
% 0.37/0.55      inference('sup-', [status(thm)], ['169', '170'])).
% 0.37/0.55  thf('172', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('173', plain,
% 0.37/0.55      ((((sk_C) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | (v1_xboole_0 @ sk_H))),
% 0.37/0.55      inference('demod', [status(thm)], ['171', '172'])).
% 0.37/0.55  thf('174', plain, (~ (v1_xboole_0 @ sk_H)),
% 0.37/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.55  thf('175', plain,
% 0.37/0.55      ((((sk_A) = (k1_xboole_0))
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['173', '174'])).
% 0.37/0.55  thf('176', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.37/0.55  thf('177', plain,
% 0.37/0.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55        | ((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | (v1_xboole_0 @ sk_G))),
% 0.37/0.55      inference('sup-', [status(thm)], ['175', '176'])).
% 0.37/0.55  thf('178', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('179', plain,
% 0.37/0.55      ((((sk_B_1) = (k1_xboole_0))
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | (v1_xboole_0 @ sk_G))),
% 0.37/0.55      inference('demod', [status(thm)], ['177', '178'])).
% 0.37/0.55  thf('180', plain, (~ (v1_xboole_0 @ sk_G)),
% 0.37/0.55      inference('sup-', [status(thm)], ['75', '76'])).
% 0.37/0.55  thf('181', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.37/0.55      inference('clc', [status(thm)], ['179', '180'])).
% 0.37/0.55  thf('182', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['79', '80'])).
% 0.37/0.55  thf('183', plain,
% 0.37/0.55      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55        | ((sk_A) = (k1_xboole_0))
% 0.37/0.55        | (v1_xboole_0 @ sk_F))),
% 0.37/0.55      inference('sup-', [status(thm)], ['181', '182'])).
% 0.37/0.55  thf('184', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('185', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_F))),
% 0.37/0.55      inference('demod', [status(thm)], ['183', '184'])).
% 0.37/0.55  thf('186', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.37/0.55      inference('sup-', [status(thm)], ['89', '90'])).
% 0.37/0.55  thf('187', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.55      inference('clc', [status(thm)], ['185', '186'])).
% 0.37/0.55  thf('188', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('189', plain, ((v1_xboole_0 @ sk_E)),
% 0.37/0.55      inference('demod', [status(thm)], ['19', '187', '188'])).
% 0.37/0.55  thf('190', plain, ($false), inference('demod', [status(thm)], ['16', '189'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
