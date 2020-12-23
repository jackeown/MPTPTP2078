%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mANGSMNduf

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:06 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 353 expanded)
%              Number of leaves         :   29 ( 122 expanded)
%              Depth                    :   27
%              Number of atoms          : 1119 (4930 expanded)
%              Number of equality atoms :   79 ( 112 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X12 ) @ X13 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
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

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('20',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X12 ) @ X14 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('28',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('29',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X15 @ X16 @ X18 @ X17 )
        = ( k2_mcart_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ sk_E ) )
        | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['26','51'])).

thf('53',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('55',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('60',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['23','60'])).

thf('62',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('63',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('64',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['13','16'])).

thf('65',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X15 @ X16 @ X18 @ X17 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k3_zfmisc_1 @ X15 @ X16 @ X18 ) )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('67',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['21'])).

thf('69',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('71',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['64','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['63','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('85',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['62','85'])).

thf('87',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['21'])).

thf('88',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['61','86','87'])).

thf('89',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['22','88'])).

thf('90',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','89'])).

thf('91',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['10','11'])).

thf('92',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','101'])).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('104',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D ) ),
    inference(demod,[status(thm)],['9','102','103'])).

thf('105',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mANGSMNduf
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:49:38 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 136 iterations in 0.059s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.22/0.52  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.52  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_G_type, type, sk_G: $i).
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
% 0.22/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.52         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.22/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.52  thf(t10_mcart_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.52       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.52         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.22/0.52          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
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
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (k1_mcart_1 @ X12) @ X13)
% 0.22/0.52          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t5_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.22/0.52          ( v1_xboole_0 @ C ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.52          | ~ (v1_xboole_0 @ X6)
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('12', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('13', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.52         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.22/0.52           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.22/0.52          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.52  thf('17', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.52  thf('18', plain,
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
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (((X15) = (k1_xboole_0))
% 0.22/0.52          | ((X16) = (k1_xboole_0))
% 0.22/0.52          | ((k6_mcart_1 @ X15 @ X16 @ X18 @ X17)
% 0.22/0.52              = (k2_mcart_1 @ (k1_mcart_1 @ X17)))
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X15 @ X16 @ X18))
% 0.22/0.52          | ((X18) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0))
% 0.22/0.52        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.22/0.52            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)
% 0.22/0.52        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)
% 0.22/0.52        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)))),
% 0.22/0.52      inference('split', [status(esa)], ['21'])).
% 0.22/0.52  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf(d1_xboole_0, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         ((r2_hidden @ (k2_mcart_1 @ X12) @ X14)
% 0.22/0.52          | ~ (r2_hidden @ X12 @ (k2_zfmisc_1 @ X13 @ X14)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.22/0.52          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.52  thf('28', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.52         (((X15) = (k1_xboole_0))
% 0.22/0.52          | ((X16) = (k1_xboole_0))
% 0.22/0.52          | ((k7_mcart_1 @ X15 @ X16 @ X18 @ X17) = (k2_mcart_1 @ X17))
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X15 @ X16 @ X18))
% 0.22/0.52          | ((X18) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      ((((sk_C) = (k1_xboole_0))
% 0.22/0.52        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.22/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('split', [status(esa)], ['21'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (((((sk_C) = (k1_xboole_0))
% 0.22/0.52         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52         | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '33'])).
% 0.22/0.52  thf('35', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.52          | ~ (v1_xboole_0 @ X6)
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.52           | ((sk_A) = (k1_xboole_0))
% 0.22/0.52           | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '37'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('39', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.22/0.52      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.52  thf(t7_ordinal1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (((sk_A) = (k1_xboole_0))
% 0.22/0.52           | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('demod', [status(thm)], ['38', '43'])).
% 0.22/0.52  thf('45', plain,
% 0.22/0.52      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '44'])).
% 0.22/0.52  thf('46', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_1))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X4 @ X5)
% 0.22/0.52          | ~ (v1_xboole_0 @ X6)
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t5_subset])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.52           | ((sk_A) = (k1_xboole_0))
% 0.22/0.52           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['45', '48'])).
% 0.22/0.52  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('demod', [status(thm)], ['49', '50'])).
% 0.22/0.52  thf('52', plain,
% 0.22/0.52      ((![X0 : $i]:
% 0.22/0.52          ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ sk_E)) | ((sk_A) = (k1_xboole_0))))
% 0.22/0.52         <= (~
% 0.22/0.52             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '51'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.53      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.22/0.53  thf('54', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.22/0.53      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.22/0.53  thf('55', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.22/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.22/0.53  thf('56', plain,
% 0.22/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['52', '55'])).
% 0.22/0.53  thf('57', plain,
% 0.22/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('58', plain,
% 0.22/0.53      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['56', '57'])).
% 0.22/0.53  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('60', plain,
% 0.22/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F)))),
% 0.22/0.53      inference('demod', [status(thm)], ['58', '59'])).
% 0.22/0.53  thf('61', plain,
% 0.22/0.53      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.22/0.53      inference('sup-', [status(thm)], ['23', '60'])).
% 0.22/0.53  thf('62', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf('63', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf('64', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.22/0.53      inference('sup-', [status(thm)], ['13', '16'])).
% 0.22/0.53  thf('65', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('66', plain,
% 0.22/0.53      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.53         (((X15) = (k1_xboole_0))
% 0.22/0.53          | ((X16) = (k1_xboole_0))
% 0.22/0.53          | ((k5_mcart_1 @ X15 @ X16 @ X18 @ X17)
% 0.22/0.53              = (k1_mcart_1 @ (k1_mcart_1 @ X17)))
% 0.22/0.53          | ~ (m1_subset_1 @ X17 @ (k3_zfmisc_1 @ X15 @ X16 @ X18))
% 0.22/0.53          | ((X18) = (k1_xboole_0)))),
% 0.22/0.53      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.22/0.53  thf('67', plain,
% 0.22/0.53      ((((sk_C) = (k1_xboole_0))
% 0.22/0.53        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G)
% 0.22/0.53            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.22/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.22/0.53  thf('68', plain,
% 0.22/0.53      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('split', [status(esa)], ['21'])).
% 0.22/0.53  thf('69', plain,
% 0.22/0.53      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.22/0.53         | ((sk_A) = (k1_xboole_0))
% 0.22/0.53         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.53  thf('70', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.22/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.53  thf('71', plain,
% 0.22/0.53      (((((sk_A) = (k1_xboole_0))
% 0.22/0.53         | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53         | ((sk_C) = (k1_xboole_0))))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.53  thf('72', plain,
% 0.22/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('73', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.53           | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53           | ((sk_A) = (k1_xboole_0))
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.22/0.53  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('75', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (((sk_B_1) = (k1_xboole_0))
% 0.22/0.53           | ((sk_A) = (k1_xboole_0))
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_F)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('demod', [status(thm)], ['73', '74'])).
% 0.22/0.53  thf('76', plain,
% 0.22/0.53      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['64', '75'])).
% 0.22/0.53  thf('77', plain,
% 0.22/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('78', plain,
% 0.22/0.53      ((![X0 : $i]:
% 0.22/0.53          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.53           | ((sk_A) = (k1_xboole_0))
% 0.22/0.53           | ~ (r2_hidden @ X0 @ sk_E)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['76', '77'])).
% 0.22/0.53  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('80', plain,
% 0.22/0.53      ((![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('demod', [status(thm)], ['78', '79'])).
% 0.22/0.53  thf('81', plain,
% 0.22/0.53      ((((sk_A) = (k1_xboole_0)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['63', '80'])).
% 0.22/0.53  thf('82', plain,
% 0.22/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('83', plain,
% 0.22/0.53      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_D)))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.22/0.53  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('85', plain,
% 0.22/0.53      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D))
% 0.22/0.53         <= (~
% 0.22/0.53             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)))),
% 0.22/0.53      inference('demod', [status(thm)], ['83', '84'])).
% 0.22/0.53  thf('86', plain,
% 0.22/0.53      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['62', '85'])).
% 0.22/0.53  thf('87', plain,
% 0.22/0.53      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)) | 
% 0.22/0.53       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_D)) | 
% 0.22/0.53       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_F))),
% 0.22/0.53      inference('split', [status(esa)], ['21'])).
% 0.22/0.53  thf('88', plain,
% 0.22/0.53      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E))),
% 0.22/0.53      inference('sat_resolution*', [status(thm)], ['61', '86', '87'])).
% 0.22/0.53  thf('89', plain,
% 0.22/0.53      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_G) @ sk_E)),
% 0.22/0.53      inference('simpl_trail', [status(thm)], ['22', '88'])).
% 0.22/0.53  thf('90', plain,
% 0.22/0.53      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.22/0.53        | ((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['20', '89'])).
% 0.22/0.53  thf('91', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf('92', plain,
% 0.22/0.53      ((((sk_A) = (k1_xboole_0))
% 0.22/0.53        | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53        | ((sk_C) = (k1_xboole_0)))),
% 0.22/0.53      inference('demod', [status(thm)], ['90', '91'])).
% 0.22/0.53  thf('93', plain,
% 0.22/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('94', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.53          | ((sk_B_1) = (k1_xboole_0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.53      inference('sup-', [status(thm)], ['92', '93'])).
% 0.22/0.53  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('96', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (((sk_B_1) = (k1_xboole_0))
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_F))),
% 0.22/0.53      inference('demod', [status(thm)], ['94', '95'])).
% 0.22/0.53  thf('97', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '96'])).
% 0.22/0.53  thf('98', plain,
% 0.22/0.53      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.22/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.53  thf('99', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.22/0.53          | ((sk_A) = (k1_xboole_0))
% 0.22/0.53          | ~ (r2_hidden @ X0 @ sk_E))),
% 0.22/0.53      inference('sup-', [status(thm)], ['97', '98'])).
% 0.22/0.53  thf('100', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('101', plain,
% 0.22/0.53      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E))),
% 0.22/0.53      inference('demod', [status(thm)], ['99', '100'])).
% 0.22/0.53  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['12', '101'])).
% 0.22/0.53  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.53      inference('sup-', [status(thm)], ['39', '42'])).
% 0.22/0.53  thf('104', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '102', '103'])).
% 0.22/0.53  thf('105', plain, ($false), inference('sup-', [status(thm)], ['6', '104'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
