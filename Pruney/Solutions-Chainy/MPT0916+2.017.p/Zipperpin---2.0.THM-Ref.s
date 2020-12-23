%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XzvPqvTu0C

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 394 expanded)
%              Number of leaves         :   30 ( 133 expanded)
%              Depth                    :   27
%              Number of atoms          : 1131 (5172 expanded)
%              Number of equality atoms :   79 ( 111 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_D @ sk_A ),
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
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('14',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('19',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('23',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( r1_xboole_0 @ X3 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X4 @ X5 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('32',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf('40',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['32','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('50',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('52',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['50','55'])).

thf('57',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('62',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X16 @ X17 @ X19 @ X18 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k3_zfmisc_1 @ X16 @ X17 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('65',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['15'])).

thf('67',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('70',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('73',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('75',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('77',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('79',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('81',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('83',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(clc,[status(thm)],['81','82'])).

thf('84',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['9','10'])).

thf('85',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('89',plain,(
    r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('91',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['62','89','90'])).

thf('92',plain,(
    ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['16','91'])).

thf('93',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','92'])).

thf('94',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k3_zfmisc_1 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('96',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X13 ) @ X15 )
      | ~ ( r2_hidden @ X13 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','98'])).

thf('100',plain,(
    r1_tarski @ sk_F @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('101',plain,
    ( ( r1_tarski @ sk_F @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('103',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ sk_F ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('105',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    r1_tarski @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('107',plain,
    ( ( r1_tarski @ sk_E @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('109',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['30'])).

thf('114',plain,(
    v1_xboole_0 @ sk_D ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['8','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XzvPqvTu0C
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:06:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 105 iterations in 0.053s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.52  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_G_type, type, sk_G: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(t76_mcart_1, conjecture,
% 0.22/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ![E:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.22/0.52           ( ![F:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.22/0.52               ( ![G:$i]:
% 0.22/0.52                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.52                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.22/0.52                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.22/0.52                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.22/0.52                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52          ( ![E:$i]:
% 0.22/0.52            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.22/0.52              ( ![F:$i]:
% 0.22/0.52                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.22/0.52                  ( ![G:$i]:
% 0.22/0.52                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.52                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.22/0.52                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.22/0.52                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.22/0.52                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.22/0.52  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(d3_zfmisc_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.22/0.52       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.22/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.52  thf(t10_mcart_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.52         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.52          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((r2_hidden @ (k1_mcart_1 @ X13) @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf(d1_xboole_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('8', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('9', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('11', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t50_mcart_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ~( ![D:$i]:
% 0.22/0.52               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.22/0.52                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.52                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.52                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.22/0.52                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.22/0.52                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (((X16) = (k1_xboole_0))
% 0.22/0.52          | ((X17) = (k1_xboole_0))
% 0.22/0.52          | ((k7_mcart_1 @ X16 @ X17 @ X19 @ X18) = (k2_mcart_1 @ X18))
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.22/0.52          | ((X19) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0))
% 0.22/0.52        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.22/0.52        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.22/0.52        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (((X16) = (k1_xboole_0))
% 0.22/0.52          | ((X17) = (k1_xboole_0))
% 0.22/0.52          | ((k5_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.22/0.52              = (k1_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.22/0.52          | ((X19) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0))
% 0.22/0.52        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.22/0.52            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('26', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['23', '26'])).
% 0.22/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.52  thf('28', plain, (![X3 : $i]: (r1_xboole_0 @ X3 @ k1_xboole_0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.52  thf(t68_xboole_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.22/0.52       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X4 @ X5)
% 0.22/0.52          | (v1_xboole_0 @ X6)
% 0.22/0.52          | ~ (r1_tarski @ X6 @ X4)
% 0.22/0.52          | ~ (r1_tarski @ X6 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.22/0.52          | ~ (r1_tarski @ X1 @ X0)
% 0.22/0.52          | (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | (v1_xboole_0 @ sk_F)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '31'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.22/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.22/0.52          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.52          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k3_zfmisc_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['33', '38'])).
% 0.22/0.52  thf('40', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('42', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.22/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('clc', [status(thm)], ['32', '43'])).
% 0.22/0.52  thf('45', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]:
% 0.22/0.52         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('47', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['44', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('54', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.52  thf('55', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.22/0.52  thf('56', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('clc', [status(thm)], ['50', '55'])).
% 0.22/0.52  thf('57', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['56', '57'])).
% 0.22/0.52  thf('59', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_D))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (((X16) = (k1_xboole_0))
% 0.22/0.52          | ((X17) = (k1_xboole_0))
% 0.22/0.52          | ((k6_mcart_1 @ X16 @ X17 @ X19 @ X18)
% 0.22/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ X18)))
% 0.22/0.52          | ~ (m1_subset_1 @ X18 @ (k3_zfmisc_1 @ X16 @ X17 @ X19))
% 0.22/0.52          | ((X19) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0))
% 0.22/0.52        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.22/0.52            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['63', '64'])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('67', plain,
% 0.22/0.52      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.52  thf('68', plain,
% 0.22/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.22/0.52          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('70', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.22/0.52      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.52  thf('71', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('demod', [status(thm)], ['67', '70'])).
% 0.22/0.52  thf('72', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('73', plain,
% 0.22/0.52      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['71', '72'])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('75', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | (v1_xboole_0 @ sk_F)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.52  thf('76', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('clc', [status(thm)], ['75', '76'])).
% 0.22/0.52  thf('78', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['77', '78'])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('81', plain,
% 0.22/0.52      (((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['79', '80'])).
% 0.22/0.52  thf('82', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('clc', [status(thm)], ['81', '82'])).
% 0.22/0.52  thf('84', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.52  thf('85', plain,
% 0.22/0.52      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['83', '84'])).
% 0.22/0.52  thf('86', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('87', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_D))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['85', '86'])).
% 0.22/0.52  thf('88', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.52  thf('89', plain,
% 0.22/0.52      (((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['87', '88'])).
% 0.22/0.52  thf('90', plain,
% 0.22/0.52      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)) | 
% 0.22/0.52       ~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.22/0.52       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.22/0.52      inference('split', [status(esa)], ['15'])).
% 0.22/0.52  thf('91', plain,
% 0.22/0.52      (~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['62', '89', '90'])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      (~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)),
% 0.22/0.52      inference('simpl_trail', [status(thm)], ['16', '91'])).
% 0.22/0.52  thf('93', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.22/0.52        | ((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '92'])).
% 0.22/0.52  thf('94', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         ((k3_zfmisc_1 @ X10 @ X11 @ X12)
% 0.22/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11) @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X13) @ X15)
% 0.22/0.52          | ~ (r2_hidden @ X13 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('97', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.52          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['95', '96'])).
% 0.22/0.52  thf('98', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['94', '97'])).
% 0.22/0.52  thf('99', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['93', '98'])).
% 0.22/0.52  thf('100', plain, ((r1_tarski @ sk_F @ sk_C)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('101', plain,
% 0.22/0.52      (((r1_tarski @ sk_F @ k1_xboole_0)
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['99', '100'])).
% 0.22/0.52  thf('102', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('103', plain,
% 0.22/0.52      ((((sk_A) = (k1_xboole_0))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | (v1_xboole_0 @ sk_F))),
% 0.22/0.52      inference('sup-', [status(thm)], ['101', '102'])).
% 0.22/0.52  thf('104', plain, (~ (v1_xboole_0 @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.52  thf('105', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('clc', [status(thm)], ['103', '104'])).
% 0.22/0.52  thf('106', plain, ((r1_tarski @ sk_E @ sk_B_1)),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.52  thf('107', plain,
% 0.22/0.52      (((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['105', '106'])).
% 0.22/0.52  thf('108', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('109', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['107', '108'])).
% 0.22/0.52  thf('110', plain, (~ (v1_xboole_0 @ sk_E)),
% 0.22/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.22/0.52  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('clc', [status(thm)], ['109', '110'])).
% 0.22/0.52  thf('112', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['11', '111'])).
% 0.22/0.52  thf('113', plain,
% 0.22/0.52      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('condensation', [status(thm)], ['30'])).
% 0.22/0.52  thf('114', plain, ((v1_xboole_0 @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['112', '113'])).
% 0.22/0.52  thf('115', plain, ($false), inference('demod', [status(thm)], ['8', '114'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
