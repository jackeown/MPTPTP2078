%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OxlFJfd7rn

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:08 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 291 expanded)
%              Number of leaves         :   25 ( 100 expanded)
%              Depth                    :   24
%              Number of atoms          : 1052 (4604 expanded)
%              Number of equality atoms :   81 ( 114 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X6 ) @ X7 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( k3_zfmisc_1 @ X3 @ X4 @ X5 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
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

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k3_zfmisc_1 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('25',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('27',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('28',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('29',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X9 @ X10 @ X12 @ X11 )
        = ( k2_mcart_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k3_zfmisc_1 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('35',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['27','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['26','53'])).

thf('55',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('56',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('57',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('58',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X9 @ X10 @ X12 @ X11 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k3_zfmisc_1 @ X9 @ X10 @ X12 ) )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('60',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('62',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('64',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( sk_B = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['56','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['55','78'])).

thf('80',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('81',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['54','79','80'])).

thf('82',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['25','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D ) ),
    inference(demod,[status(thm)],['9','92','93'])).

thf('95',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OxlFJfd7rn
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.39/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.56  % Solved by: fo/fo7.sh
% 0.39/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.56  % done 96 iterations in 0.068s
% 0.39/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.56  % SZS output start Refutation
% 0.39/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.56  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.39/0.56  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.56  thf(sk_G_type, type, sk_G: $i).
% 0.39/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.56  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.56  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.39/0.56  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.39/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.39/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.56  thf(t76_mcart_1, conjecture,
% 0.39/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56       ( ![E:$i]:
% 0.39/0.56         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.39/0.56           ( ![F:$i]:
% 0.39/0.56             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.39/0.56               ( ![G:$i]:
% 0.39/0.56                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.56                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.39/0.56                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.39/0.56                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.39/0.56                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.56        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.56          ( ![E:$i]:
% 0.39/0.56            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.39/0.56              ( ![F:$i]:
% 0.39/0.56                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.39/0.56                  ( ![G:$i]:
% 0.39/0.56                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.56                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.39/0.56                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.39/0.56                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.39/0.56                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.56    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.39/0.56  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(d3_zfmisc_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.39/0.56       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.39/0.56  thf('1', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.56         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.39/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.56  thf(t10_mcart_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.39/0.56       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.39/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.39/0.56  thf('2', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.56         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.39/0.56          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.56  thf('3', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.56          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.56  thf('4', plain,
% 0.39/0.56      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.56  thf('5', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.56         ((r2_hidden @ (k1_mcart_1 @ X6) @ X7)
% 0.39/0.56          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.56  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t5_subset, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.39/0.56          ( v1_xboole_0 @ C ) ) ))).
% 0.39/0.56  thf('8', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.56          | ~ (v1_xboole_0 @ X2)
% 0.39/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.56  thf('9', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.39/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.56  thf('10', plain,
% 0.39/0.56      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.39/0.56      inference('sup-', [status(thm)], ['0', '3'])).
% 0.39/0.56  thf('11', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.56         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.39/0.56          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.56  thf('12', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('13', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('14', plain,
% 0.39/0.56      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.56         ((k3_zfmisc_1 @ X3 @ X4 @ X5)
% 0.39/0.56           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4) @ X5))),
% 0.39/0.56      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.39/0.56  thf('15', plain,
% 0.39/0.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.56         ((r2_hidden @ (k2_mcart_1 @ X6) @ X8)
% 0.39/0.56          | ~ (r2_hidden @ X6 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.39/0.56  thf('16', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.39/0.56          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.56  thf('17', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.39/0.56  thf('18', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf(t50_mcart_1, axiom,
% 0.39/0.56    (![A:$i,B:$i,C:$i]:
% 0.39/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.56          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.39/0.56          ( ~( ![D:$i]:
% 0.39/0.56               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.39/0.56                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.39/0.56                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.39/0.56                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.39/0.56                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.39/0.56                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.39/0.56  thf('19', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.56         (((X9) = (k1_xboole_0))
% 0.39/0.56          | ((X10) = (k1_xboole_0))
% 0.39/0.56          | ((k6_mcart_1 @ X9 @ X10 @ X12 @ X11)
% 0.39/0.56              = (k2_mcart_1 @ (k1_mcart_1 @ X11)))
% 0.39/0.56          | ~ (m1_subset_1 @ X11 @ (k3_zfmisc_1 @ X9 @ X10 @ X12))
% 0.39/0.56          | ((X12) = (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.39/0.56  thf('20', plain,
% 0.39/0.56      ((((sk_C) = (k1_xboole_0))
% 0.39/0.56        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.39/0.56            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.39/0.56        | ((sk_B) = (k1_xboole_0))
% 0.39/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.56  thf('21', plain,
% 0.39/0.56      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)
% 0.39/0.56        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E)
% 0.39/0.56        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('22', plain,
% 0.39/0.56      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E))
% 0.39/0.56         <= (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E)))),
% 0.39/0.56      inference('split', [status(esa)], ['21'])).
% 0.39/0.56  thf('23', plain,
% 0.39/0.56      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.39/0.56         | ((sk_A) = (k1_xboole_0))
% 0.39/0.56         | ((sk_B) = (k1_xboole_0))
% 0.39/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['20', '22'])).
% 0.39/0.56  thf('24', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('25', plain,
% 0.39/0.56      (((((sk_A) = (k1_xboole_0))
% 0.39/0.56         | ((sk_B) = (k1_xboole_0))
% 0.39/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E)))),
% 0.39/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.39/0.56  thf('26', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('27', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('28', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.39/0.56  thf('29', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('30', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.56         (((X9) = (k1_xboole_0))
% 0.39/0.56          | ((X10) = (k1_xboole_0))
% 0.39/0.56          | ((k7_mcart_1 @ X9 @ X10 @ X12 @ X11) = (k2_mcart_1 @ X11))
% 0.39/0.56          | ~ (m1_subset_1 @ X11 @ (k3_zfmisc_1 @ X9 @ X10 @ X12))
% 0.39/0.56          | ((X12) = (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.39/0.56  thf('31', plain,
% 0.39/0.56      ((((sk_C) = (k1_xboole_0))
% 0.39/0.56        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.39/0.56        | ((sk_B) = (k1_xboole_0))
% 0.39/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.39/0.56  thf('32', plain,
% 0.39/0.56      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('split', [status(esa)], ['21'])).
% 0.39/0.56  thf('33', plain,
% 0.39/0.56      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.39/0.56         | ((sk_A) = (k1_xboole_0))
% 0.39/0.56         | ((sk_B) = (k1_xboole_0))
% 0.39/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.56  thf('34', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.39/0.56  thf('35', plain,
% 0.39/0.56      (((((sk_A) = (k1_xboole_0))
% 0.39/0.56         | ((sk_B) = (k1_xboole_0))
% 0.39/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.56  thf('36', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('37', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.56          | ~ (v1_xboole_0 @ X2)
% 0.39/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.56  thf('38', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf('39', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56           | ((sk_B) = (k1_xboole_0))
% 0.39/0.56           | ((sk_A) = (k1_xboole_0))
% 0.39/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['35', '38'])).
% 0.39/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.56  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('41', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (((sk_B) = (k1_xboole_0))
% 0.39/0.56           | ((sk_A) = (k1_xboole_0))
% 0.39/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('demod', [status(thm)], ['39', '40'])).
% 0.39/0.56  thf('42', plain,
% 0.39/0.56      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['28', '41'])).
% 0.39/0.56  thf('43', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('44', plain,
% 0.39/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.39/0.56          | ~ (v1_xboole_0 @ X2)
% 0.39/0.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t5_subset])).
% 0.39/0.56  thf('45', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('46', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56           | ((sk_A) = (k1_xboole_0))
% 0.39/0.56           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['42', '45'])).
% 0.39/0.56  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('48', plain,
% 0.39/0.56      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.56  thf('49', plain,
% 0.39/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['27', '48'])).
% 0.39/0.56  thf('50', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.39/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.56  thf('51', plain,
% 0.39/0.56      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['49', '50'])).
% 0.39/0.56  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('53', plain,
% 0.39/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.39/0.56         <= (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F)))),
% 0.39/0.56      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.56  thf('54', plain,
% 0.39/0.56      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F))),
% 0.39/0.56      inference('sup-', [status(thm)], ['26', '53'])).
% 0.39/0.56  thf('55', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('56', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.39/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.56  thf('57', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.39/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.39/0.56  thf('58', plain, ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.39/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.56  thf('59', plain,
% 0.39/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.56         (((X9) = (k1_xboole_0))
% 0.39/0.56          | ((X10) = (k1_xboole_0))
% 0.39/0.56          | ((k5_mcart_1 @ X9 @ X10 @ X12 @ X11)
% 0.39/0.56              = (k1_mcart_1 @ (k1_mcart_1 @ X11)))
% 0.39/0.56          | ~ (m1_subset_1 @ X11 @ (k3_zfmisc_1 @ X9 @ X10 @ X12))
% 0.39/0.56          | ((X12) = (k1_xboole_0)))),
% 0.39/0.56      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.39/0.56  thf('60', plain,
% 0.39/0.56      ((((sk_C) = (k1_xboole_0))
% 0.39/0.56        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 0.39/0.56            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.39/0.56        | ((sk_B) = (k1_xboole_0))
% 0.39/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.56  thf('61', plain,
% 0.39/0.56      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('split', [status(esa)], ['21'])).
% 0.39/0.56  thf('62', plain,
% 0.39/0.56      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.39/0.56         | ((sk_A) = (k1_xboole_0))
% 0.39/0.56         | ((sk_B) = (k1_xboole_0))
% 0.39/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.56  thf('63', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.39/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.56  thf('64', plain,
% 0.39/0.56      (((((sk_A) = (k1_xboole_0))
% 0.39/0.56         | ((sk_B) = (k1_xboole_0))
% 0.39/0.56         | ((sk_C) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.39/0.56  thf('65', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf('66', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56           | ((sk_B) = (k1_xboole_0))
% 0.39/0.56           | ((sk_A) = (k1_xboole_0))
% 0.39/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.39/0.56  thf('67', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('68', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (((sk_B) = (k1_xboole_0))
% 0.39/0.56           | ((sk_A) = (k1_xboole_0))
% 0.39/0.56           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('demod', [status(thm)], ['66', '67'])).
% 0.39/0.56  thf('69', plain,
% 0.39/0.56      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['57', '68'])).
% 0.39/0.56  thf('70', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('71', plain,
% 0.39/0.56      ((![X0 : $i]:
% 0.39/0.56          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56           | ((sk_A) = (k1_xboole_0))
% 0.39/0.56           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.39/0.56  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('73', plain,
% 0.39/0.56      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('demod', [status(thm)], ['71', '72'])).
% 0.39/0.56  thf('74', plain,
% 0.39/0.56      ((((sk_A) = (k1_xboole_0)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['56', '73'])).
% 0.39/0.56  thf('75', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.39/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.56  thf('76', plain,
% 0.39/0.56      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.56  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('78', plain,
% 0.39/0.56      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.39/0.56         <= (~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)))),
% 0.39/0.56      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.56  thf('79', plain,
% 0.39/0.56      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D))),
% 0.39/0.56      inference('sup-', [status(thm)], ['55', '78'])).
% 0.39/0.56  thf('80', plain,
% 0.39/0.56      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E)) | 
% 0.39/0.56       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_D)) | 
% 0.39/0.56       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_F))),
% 0.39/0.56      inference('split', [status(esa)], ['21'])).
% 0.39/0.56  thf('81', plain,
% 0.39/0.56      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_G) @ sk_E))),
% 0.39/0.56      inference('sat_resolution*', [status(thm)], ['54', '79', '80'])).
% 0.39/0.56  thf('82', plain,
% 0.39/0.56      ((((sk_A) = (k1_xboole_0))
% 0.39/0.56        | ((sk_B) = (k1_xboole_0))
% 0.39/0.56        | ((sk_C) = (k1_xboole_0)))),
% 0.39/0.56      inference('simpl_trail', [status(thm)], ['25', '81'])).
% 0.39/0.56  thf('83', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.56  thf('84', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56          | ((sk_B) = (k1_xboole_0))
% 0.39/0.56          | ((sk_A) = (k1_xboole_0))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.56  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('86', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (((sk_B) = (k1_xboole_0))
% 0.39/0.56          | ((sk_A) = (k1_xboole_0))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.39/0.56      inference('demod', [status(thm)], ['84', '85'])).
% 0.39/0.56  thf('87', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.56      inference('sup-', [status(thm)], ['17', '86'])).
% 0.39/0.56  thf('88', plain,
% 0.39/0.56      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.56  thf('89', plain,
% 0.39/0.56      (![X0 : $i]:
% 0.39/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.56          | ((sk_A) = (k1_xboole_0))
% 0.39/0.56          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.56      inference('sup-', [status(thm)], ['87', '88'])).
% 0.39/0.56  thf('90', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('91', plain,
% 0.39/0.56      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.39/0.56      inference('demod', [status(thm)], ['89', '90'])).
% 0.39/0.56  thf('92', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.56      inference('sup-', [status(thm)], ['12', '91'])).
% 0.39/0.56  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.56  thf('94', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)),
% 0.39/0.56      inference('demod', [status(thm)], ['9', '92', '93'])).
% 0.39/0.56  thf('95', plain, ($false), inference('sup-', [status(thm)], ['6', '94'])).
% 0.39/0.56  
% 0.39/0.56  % SZS output end Refutation
% 0.39/0.56  
% 0.39/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
