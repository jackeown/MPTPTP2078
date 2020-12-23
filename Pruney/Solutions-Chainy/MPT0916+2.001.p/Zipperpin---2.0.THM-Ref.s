%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BIFwGwDdX4

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 373 expanded)
%              Number of leaves         :   27 ( 128 expanded)
%              Depth                    :   26
%              Number of atoms          : 1141 (4982 expanded)
%              Number of equality atoms :   80 ( 111 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(t76_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
     => ! [E: $i] :
          ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
         => ! [F: $i] :
              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                 => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                   => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                      & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                      & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
       => ! [E: $i] :
            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) )
               => ! [G: $i] :
                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) )
                   => ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) )
                     => ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D )
                        & ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E )
                        & ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
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

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X11 @ X12 @ X14 @ X13 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('14',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X11 @ X12 @ X14 @ X13 )
        = ( k2_mcart_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('30',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(clc,[status(thm)],['33','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_zfmisc_1 @ X5 @ X6 @ X7 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('54',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_zfmisc_1 @ X1 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('65',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('69',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('71',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X11 = k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X11 @ X12 @ X14 @ X13 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k3_zfmisc_1 @ X11 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('73',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('75',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('82',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('84',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('90',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('94',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('96',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['69','94','95'])).

thf('97',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['16','96'])).

thf('98',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','97'])).

thf('99',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('100',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('101',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('104',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('110',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('112',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('114',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('116',plain,(
    v1_xboole_0 @ sk_D ),
    inference(demod,[status(thm)],['11','114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['8','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BIFwGwDdX4
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:53:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 97 iterations in 0.050s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.50  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(t76_mcart_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ![E:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.20/0.50           ( ![F:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.20/0.50               ( ![G:$i]:
% 0.20/0.50                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.50                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.20/0.50                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.20/0.50                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50          ( ![E:$i]:
% 0.20/0.50            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.20/0.50              ( ![F:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.20/0.50                  ( ![G:$i]:
% 0.20/0.50                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.20/0.50                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.20/0.50                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.20/0.50                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.20/0.50  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d3_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.50       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.50  thf(t10_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.50       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.50         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k1_mcart_1 @ X8) @ X9)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k1_mcart_1 @ X8) @ X9)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.50  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf(d1_xboole_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('8', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_subset_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.50          | (v1_xboole_0 @ X3)
% 0.20/0.50          | ~ (v1_xboole_0 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.50  thf('11', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t50_mcart_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50          ( ~( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.50                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.50                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.50                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.50                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.50                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (((X11) = (k1_xboole_0))
% 0.20/0.50          | ((X12) = (k1_xboole_0))
% 0.20/0.50          | ((k6_mcart_1 @ X11 @ X12 @ X14 @ X13)
% 0.20/0.50              = (k2_mcart_1 @ (k1_mcart_1 @ X13)))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X11 @ X12 @ X14))
% 0.20/0.50          | ((X14) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.20/0.50            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.20/0.50        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.20/0.50        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.20/0.50      inference('split', [status(esa)], ['15'])).
% 0.20/0.50  thf('17', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k2_mcart_1 @ X8) @ X10)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.20/0.50      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (((X11) = (k1_xboole_0))
% 0.20/0.50          | ((X12) = (k1_xboole_0))
% 0.20/0.50          | ((k7_mcart_1 @ X11 @ X12 @ X14 @ X13) = (k2_mcart_1 @ X13))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X11 @ X12 @ X14))
% 0.20/0.50          | ((X14) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('split', [status(esa)], ['15'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((((sk_C) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '26'])).
% 0.20/0.50  thf('28', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.50          | (v1_xboole_0 @ X3)
% 0.20/0.50          | ~ (v1_xboole_0 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.50  thf('30', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | (v1_xboole_0 @ sk_F)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.50  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.50  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | (v1_xboole_0 @ sk_F)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k2_mcart_1 @ X8) @ X10)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['34', '39'])).
% 0.20/0.50  thf('41', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('43', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.50  thf('45', plain,
% 0.20/0.50      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('clc', [status(thm)], ['33', '44'])).
% 0.20/0.50  thf('46', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain,
% 0.20/0.50      (![X3 : $i, X4 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.50          | (v1_xboole_0 @ X3)
% 0.20/0.50          | ~ (v1_xboole_0 @ X4))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.20/0.50  thf('48', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | (v1_xboole_0 @ sk_E)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.50  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((k3_zfmisc_1 @ X5 @ X6 @ X7)
% 0.20/0.50           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6) @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.50  thf('54', plain,
% 0.20/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('55', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k1_mcart_1 @ X8) @ X9)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.50  thf('56', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.20/0.50          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.20/0.50          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.20/0.50      inference('sup+', [status(thm)], ['53', '58'])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_zfmisc_1 @ X1 @ X0 @ X2)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['52', '59'])).
% 0.20/0.50  thf('61', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('62', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('63', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['51', '62'])).
% 0.20/0.50  thf('64', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('65', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.50  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('67', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_D))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.50  thf('68', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.20/0.50  thf('70', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.50         (((X11) = (k1_xboole_0))
% 0.20/0.50          | ((X12) = (k1_xboole_0))
% 0.20/0.50          | ((k5_mcart_1 @ X11 @ X12 @ X14 @ X13)
% 0.20/0.50              = (k1_mcart_1 @ (k1_mcart_1 @ X13)))
% 0.20/0.50          | ~ (m1_subset_1 @ X13 @ (k3_zfmisc_1 @ X11 @ X12 @ X14))
% 0.20/0.50          | ((X14) = (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.50  thf('73', plain,
% 0.20/0.50      ((((sk_C) = (k1_xboole_0))
% 0.20/0.50        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.20/0.50            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('split', [status(esa)], ['15'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | ((sk_C) = (k1_xboole_0))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['73', '74'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      (((((sk_C) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['70', '75'])).
% 0.20/0.50  thf('77', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | (v1_xboole_0 @ sk_F)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      (((((sk_A) = (k1_xboole_0))
% 0.20/0.50         | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50         | (v1_xboole_0 @ sk_F)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.50  thf('81', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50         | ((sk_A) = (k1_xboole_0))
% 0.20/0.50         | (v1_xboole_0 @ sk_E)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('clc', [status(thm)], ['86', '87'])).
% 0.20/0.50  thf('89', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (((~ (v1_xboole_0 @ k1_xboole_0) | (v1_xboole_0 @ sk_D)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['88', '89'])).
% 0.20/0.50  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (((v1_xboole_0 @ sk_D))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.20/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.20/0.50  thf('93', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['92', '93'])).
% 0.20/0.50  thf('95', plain,
% 0.20/0.50      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.20/0.50       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)) | 
% 0.20/0.50       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.20/0.50      inference('split', [status(esa)], ['15'])).
% 0.20/0.50  thf('96', plain,
% 0.20/0.50      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['69', '94', '95'])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['16', '96'])).
% 0.20/0.50  thf('98', plain,
% 0.20/0.50      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['14', '97'])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.50         ((r2_hidden @ (k2_mcart_1 @ X8) @ X10)
% 0.20/0.50          | ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X9 @ X10)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.50  thf('101', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.20/0.50      inference('sup-', [status(thm)], ['99', '100'])).
% 0.20/0.50  thf('102', plain,
% 0.20/0.50      ((((sk_A) = (k1_xboole_0))
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_C) = (k1_xboole_0)))),
% 0.20/0.50      inference('demod', [status(thm)], ['98', '101'])).
% 0.20/0.50  thf('103', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('104', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (v1_xboole_0 @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['102', '103'])).
% 0.20/0.50  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('106', plain,
% 0.20/0.50      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (v1_xboole_0 @ sk_F))),
% 0.20/0.50      inference('demod', [status(thm)], ['104', '105'])).
% 0.20/0.50  thf('107', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.20/0.50      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.50  thf('108', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.50      inference('clc', [status(thm)], ['106', '107'])).
% 0.20/0.50  thf('109', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('110', plain,
% 0.20/0.50      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.50        | ((sk_A) = (k1_xboole_0))
% 0.20/0.50        | (v1_xboole_0 @ sk_E))),
% 0.20/0.50      inference('sup-', [status(thm)], ['108', '109'])).
% 0.20/0.50  thf('111', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('112', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.20/0.50      inference('demod', [status(thm)], ['110', '111'])).
% 0.20/0.50  thf('113', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.20/0.50      inference('sup-', [status(thm)], ['60', '61'])).
% 0.20/0.50  thf('114', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.50      inference('clc', [status(thm)], ['112', '113'])).
% 0.20/0.50  thf('115', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.50      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.50  thf('116', plain, ((v1_xboole_0 @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '114', '115'])).
% 0.20/0.50  thf('117', plain, ($false), inference('demod', [status(thm)], ['8', '116'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
