%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OyX6p2esQK

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:05 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 739 expanded)
%              Number of leaves         :   35 ( 251 expanded)
%              Depth                    :   29
%              Number of atoms          : 1625 (7813 expanded)
%              Number of equality atoms :  122 ( 260 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('0',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

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

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('11',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(condensation,[status(thm)],['19'])).

thf('21',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('22',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('32',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('38',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['20','47'])).

thf('49',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('51',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('55',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('58',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
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

thf('62',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X35 @ X36 @ X38 @ X37 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k3_zfmisc_1 @ X35 @ X36 @ X38 ) )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('63',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['64'])).

thf('66',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('67',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('70',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('72',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['56','59'])).

thf('73',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X35 @ X36 @ X38 @ X37 )
        = ( k2_mcart_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k3_zfmisc_1 @ X35 @ X36 @ X38 ) )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('75',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['64'])).

thf('77',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['56','59'])).

thf('79',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('82',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_F @ sk_C_1 )
    = sk_F ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_xboole_0 @ sk_F @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
        | ( sk_B_2 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('89',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['72','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('93',plain,(
    r1_tarski @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_B_2 )
    = sk_E ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( ( k3_xboole_0 @ sk_E @ k1_xboole_0 )
        = sk_E )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['90','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('98',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['9','16'])).

thf('100',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0 = sk_E )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('102',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('103',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_xboole_0 @ X15 @ X16 )
        = X15 )
      | ~ ( r1_tarski @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','109'])).

thf('111',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( v1_xboole_0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['100','110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','46'])).

thf('113',plain,
    ( ( k1_xboole_0 = sk_E )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['26','45'])).

thf('115',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_D @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['71','115'])).

thf('117',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['70','116'])).

thf('118',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','109'])).

thf('119',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('121',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X32 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('122',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['56','59'])).

thf('124',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( X36 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X35 @ X36 @ X38 @ X37 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X37 ) ) )
      | ~ ( m1_subset_1 @ X37 @ ( k3_zfmisc_1 @ X35 @ X36 @ X38 ) )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('126',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['64'])).

thf('128',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['120','121'])).

thf('130',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_xboole_0 @ sk_F @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('132',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
        | ( sk_B_2 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('134',plain,
    ( ! [X0: $i] :
        ( ( sk_B_2 = k1_xboole_0 )
        | ( sk_A = k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['123','134'])).

thf('136',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_B_2 )
    = sk_E ),
    inference('sup-',[status(thm)],['93','94'])).

thf('137',plain,
    ( ( ( ( k3_xboole_0 @ sk_E @ k1_xboole_0 )
        = sk_E )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('139',plain,
    ( ( ( k1_xboole_0 = sk_E )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_A )
    = sk_D ),
    inference('sup-',[status(thm)],['7','8'])).

thf('141',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ~ ( r1_xboole_0 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_D @ k1_xboole_0 )
        | ( k1_xboole_0 = sk_E )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['139','142'])).

thf('144',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('145',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 = sk_E )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k1_xboole_0 = sk_E )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['122','145'])).

thf('147',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('149',plain,(
    ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_D @ k1_xboole_0 @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( k3_zfmisc_1 @ X29 @ X30 @ X31 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('157',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','109'])).

thf('159',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D ),
    inference(demod,[status(thm)],['150','157','158'])).

thf('160',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['64'])).

thf('161',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['119','159','160'])).

thf('162',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(simpl_trail,[status(thm)],['65','161'])).

thf('163',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','162'])).

thf('164',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['53','54'])).

thf('165',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_F )
      | ~ ( r1_xboole_0 @ sk_F @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_F @ k1_xboole_0 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','169'])).

thf('171',plain,
    ( ( k3_xboole_0 @ sk_E @ sk_B_2 )
    = sk_E ),
    inference('sup-',[status(thm)],['93','94'])).

thf('172',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_E )
      | ~ ( r1_xboole_0 @ sk_E @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['170','173'])).

thf('175',plain,(
    ! [X20: $i] :
      ( r1_xboole_0 @ X20 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','176'])).

thf('178',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','109'])).

thf('179',plain,(
    $false ),
    inference(demod,[status(thm)],['48','177','178'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OyX6p2esQK
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.64/1.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.91  % Solved by: fo/fo7.sh
% 1.64/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.91  % done 4430 iterations in 1.454s
% 1.64/1.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.91  % SZS output start Refutation
% 1.64/1.91  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.64/1.91  thf(sk_B_type, type, sk_B: $i > $i).
% 1.64/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.64/1.91  thf(sk_B_2_type, type, sk_B_2: $i).
% 1.64/1.91  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.64/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.91  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.64/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.64/1.91  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 1.64/1.91  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 1.64/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.64/1.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.64/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.64/1.91  thf(sk_F_type, type, sk_F: $i).
% 1.64/1.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.64/1.91  thf(sk_G_type, type, sk_G: $i).
% 1.64/1.91  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.64/1.91  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 1.64/1.91  thf(sk_E_type, type, sk_E: $i).
% 1.64/1.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.64/1.91  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.64/1.91  thf(sk_D_type, type, sk_D: $i).
% 1.64/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.91  thf(t6_mcart_1, axiom,
% 1.64/1.91    (![A:$i]:
% 1.64/1.91     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.64/1.91          ( ![B:$i]:
% 1.64/1.91            ( ~( ( r2_hidden @ B @ A ) & 
% 1.64/1.91                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 1.64/1.91                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 1.64/1.91                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 1.64/1.91                       ( r2_hidden @ G @ B ) ) =>
% 1.64/1.91                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 1.64/1.91  thf('0', plain,
% 1.64/1.91      (![X39 : $i]:
% 1.64/1.91         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X39) @ X39))),
% 1.64/1.91      inference('cnf', [status(esa)], [t6_mcart_1])).
% 1.64/1.91  thf(d1_xboole_0, axiom,
% 1.64/1.91    (![A:$i]:
% 1.64/1.91     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.64/1.91  thf('1', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf('2', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('3', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('4', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.64/1.91      inference('sup+', [status(thm)], ['2', '3'])).
% 1.64/1.91  thf(t76_mcart_1, conjecture,
% 1.64/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.64/1.91     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.91       ( ![E:$i]:
% 1.64/1.91         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.64/1.91           ( ![F:$i]:
% 1.64/1.91             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 1.64/1.91               ( ![G:$i]:
% 1.64/1.91                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.64/1.91                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.64/1.91                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 1.64/1.91                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 1.64/1.91                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 1.64/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.64/1.91        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 1.64/1.91          ( ![E:$i]:
% 1.64/1.91            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 1.64/1.91              ( ![F:$i]:
% 1.64/1.91                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 1.64/1.91                  ( ![G:$i]:
% 1.64/1.91                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.64/1.91                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 1.64/1.91                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 1.64/1.91                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 1.64/1.91                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 1.64/1.91    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 1.64/1.91  thf('5', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf(t3_subset, axiom,
% 1.64/1.91    (![A:$i,B:$i]:
% 1.64/1.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.64/1.91  thf('6', plain,
% 1.64/1.91      (![X26 : $i, X27 : $i]:
% 1.64/1.91         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.64/1.91  thf('7', plain, ((r1_tarski @ sk_D @ sk_A)),
% 1.64/1.91      inference('sup-', [status(thm)], ['5', '6'])).
% 1.64/1.91  thf(t28_xboole_1, axiom,
% 1.64/1.91    (![A:$i,B:$i]:
% 1.64/1.91     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.64/1.91  thf('8', plain,
% 1.64/1.91      (![X15 : $i, X16 : $i]:
% 1.64/1.91         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.64/1.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.64/1.91  thf('9', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 1.64/1.91      inference('sup-', [status(thm)], ['7', '8'])).
% 1.64/1.91  thf('10', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.64/1.91  thf('11', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('12', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup+', [status(thm)], ['10', '11'])).
% 1.64/1.91  thf('13', plain,
% 1.64/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf(t4_xboole_0, axiom,
% 1.64/1.91    (![A:$i,B:$i]:
% 1.64/1.91     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.64/1.91            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.64/1.91       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.64/1.91            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.64/1.91  thf('14', plain,
% 1.64/1.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.64/1.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.64/1.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.64/1.91  thf('15', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['13', '14'])).
% 1.64/1.91  thf('16', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['12', '15'])).
% 1.64/1.91  thf('17', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 1.64/1.91      inference('sup+', [status(thm)], ['9', '16'])).
% 1.64/1.91  thf('18', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (v1_xboole_0 @ X0)
% 1.64/1.91          | ~ (v1_xboole_0 @ X0)
% 1.64/1.91          | ~ (v1_xboole_0 @ sk_A)
% 1.64/1.91          | (v1_xboole_0 @ sk_D))),
% 1.64/1.91      inference('sup-', [status(thm)], ['4', '17'])).
% 1.64/1.91  thf('19', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('simplify', [status(thm)], ['18'])).
% 1.64/1.91  thf('20', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 1.64/1.91      inference('condensation', [status(thm)], ['19'])).
% 1.64/1.91  thf('21', plain,
% 1.64/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf(t10_mcart_1, axiom,
% 1.64/1.91    (![A:$i,B:$i,C:$i]:
% 1.64/1.91     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 1.64/1.91       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 1.64/1.91         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 1.64/1.91  thf('22', plain,
% 1.64/1.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.91         ((r2_hidden @ (k1_mcart_1 @ X32) @ X33)
% 1.64/1.91          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.64/1.91  thf('23', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.64/1.91          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.64/1.91      inference('sup-', [status(thm)], ['21', '22'])).
% 1.64/1.91  thf('24', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf('25', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['23', '24'])).
% 1.64/1.91  thf('26', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf(d3_zfmisc_1, axiom,
% 1.64/1.91    (![A:$i,B:$i,C:$i]:
% 1.64/1.91     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 1.64/1.91       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 1.64/1.91  thf('27', plain,
% 1.64/1.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.64/1.91         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.64/1.91           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.64/1.91      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.64/1.91  thf('28', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('29', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.64/1.91          | (r2_hidden @ (k1_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 1.64/1.91      inference('sup-', [status(thm)], ['21', '22'])).
% 1.64/1.91  thf('30', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('31', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['13', '14'])).
% 1.64/1.91  thf('32', plain,
% 1.64/1.91      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['30', '31'])).
% 1.64/1.91  thf('33', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('34', plain,
% 1.64/1.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['32', '33'])).
% 1.64/1.91  thf('35', plain,
% 1.64/1.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.64/1.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.64/1.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.64/1.91  thf('36', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['34', '35'])).
% 1.64/1.91  thf('37', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('38', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.64/1.91      inference('demod', [status(thm)], ['36', '37'])).
% 1.64/1.91  thf('39', plain,
% 1.64/1.91      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['29', '38'])).
% 1.64/1.91  thf('40', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('41', plain,
% 1.64/1.91      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['39', '40'])).
% 1.64/1.91  thf('42', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup+', [status(thm)], ['28', '41'])).
% 1.64/1.91  thf('43', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.64/1.91      inference('demod', [status(thm)], ['36', '37'])).
% 1.64/1.91  thf('44', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ X1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 1.64/1.91      inference('sup-', [status(thm)], ['42', '43'])).
% 1.64/1.91  thf('45', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.64/1.91          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['27', '44'])).
% 1.64/1.91  thf('46', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['26', '45'])).
% 1.64/1.91  thf('47', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.64/1.91      inference('sup-', [status(thm)], ['25', '46'])).
% 1.64/1.91  thf('48', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.64/1.91      inference('clc', [status(thm)], ['20', '47'])).
% 1.64/1.91  thf('49', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('50', plain,
% 1.64/1.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.64/1.91         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.64/1.91           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.64/1.91      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.64/1.91  thf('51', plain,
% 1.64/1.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.91         ((r2_hidden @ (k1_mcart_1 @ X32) @ X33)
% 1.64/1.91          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.64/1.91  thf('52', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.64/1.91          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['50', '51'])).
% 1.64/1.91  thf('53', plain,
% 1.64/1.91      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['49', '52'])).
% 1.64/1.91  thf('54', plain,
% 1.64/1.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.91         ((r2_hidden @ (k2_mcart_1 @ X32) @ X34)
% 1.64/1.91          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.64/1.91  thf('55', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 1.64/1.91      inference('sup-', [status(thm)], ['53', '54'])).
% 1.64/1.91  thf('56', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('57', plain,
% 1.64/1.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.64/1.91         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.64/1.91           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.64/1.91      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.64/1.91  thf('58', plain,
% 1.64/1.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.91         ((r2_hidden @ (k2_mcart_1 @ X32) @ X34)
% 1.64/1.91          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.64/1.91  thf('59', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 1.64/1.91          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['57', '58'])).
% 1.64/1.91  thf('60', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 1.64/1.91      inference('sup-', [status(thm)], ['56', '59'])).
% 1.64/1.91  thf('61', plain,
% 1.64/1.91      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf(t50_mcart_1, axiom,
% 1.64/1.91    (![A:$i,B:$i,C:$i]:
% 1.64/1.91     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.64/1.91          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.64/1.91          ( ~( ![D:$i]:
% 1.64/1.91               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.64/1.91                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 1.64/1.91                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.64/1.91                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 1.64/1.91                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 1.64/1.91                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 1.64/1.91  thf('62', plain,
% 1.64/1.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.64/1.91         (((X35) = (k1_xboole_0))
% 1.64/1.91          | ((X36) = (k1_xboole_0))
% 1.64/1.91          | ((k6_mcart_1 @ X35 @ X36 @ X38 @ X37)
% 1.64/1.91              = (k2_mcart_1 @ (k1_mcart_1 @ X37)))
% 1.64/1.91          | ~ (m1_subset_1 @ X37 @ (k3_zfmisc_1 @ X35 @ X36 @ X38))
% 1.64/1.91          | ((X38) = (k1_xboole_0)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.64/1.91  thf('63', plain,
% 1.64/1.91      ((((sk_C_1) = (k1_xboole_0))
% 1.64/1.91        | ((k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G)
% 1.64/1.91            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 1.64/1.91        | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91        | ((sk_A) = (k1_xboole_0)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['61', '62'])).
% 1.64/1.91  thf('64', plain,
% 1.64/1.91      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)
% 1.64/1.91        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_E)
% 1.64/1.91        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('65', plain,
% 1.64/1.91      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_E))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_E)))),
% 1.64/1.91      inference('split', [status(esa)], ['64'])).
% 1.64/1.91  thf('66', plain,
% 1.64/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf('67', plain,
% 1.64/1.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.91         ((r2_hidden @ (k2_mcart_1 @ X32) @ X34)
% 1.64/1.91          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.64/1.91  thf('68', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 1.64/1.91          | (r2_hidden @ (k2_mcart_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0))) @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['66', '67'])).
% 1.64/1.91  thf('69', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.64/1.91      inference('demod', [status(thm)], ['36', '37'])).
% 1.64/1.91  thf('70', plain,
% 1.64/1.91      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['68', '69'])).
% 1.64/1.91  thf('71', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('72', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 1.64/1.91      inference('sup-', [status(thm)], ['56', '59'])).
% 1.64/1.91  thf('73', plain,
% 1.64/1.91      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('74', plain,
% 1.64/1.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.64/1.91         (((X35) = (k1_xboole_0))
% 1.64/1.91          | ((X36) = (k1_xboole_0))
% 1.64/1.91          | ((k7_mcart_1 @ X35 @ X36 @ X38 @ X37) = (k2_mcart_1 @ X37))
% 1.64/1.91          | ~ (m1_subset_1 @ X37 @ (k3_zfmisc_1 @ X35 @ X36 @ X38))
% 1.64/1.91          | ((X38) = (k1_xboole_0)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.64/1.91  thf('75', plain,
% 1.64/1.91      ((((sk_C_1) = (k1_xboole_0))
% 1.64/1.91        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 1.64/1.91        | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91        | ((sk_A) = (k1_xboole_0)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['73', '74'])).
% 1.64/1.91  thf('76', plain,
% 1.64/1.91      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('split', [status(esa)], ['64'])).
% 1.64/1.91  thf('77', plain,
% 1.64/1.91      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 1.64/1.91         | ((sk_A) = (k1_xboole_0))
% 1.64/1.91         | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91         | ((sk_C_1) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['75', '76'])).
% 1.64/1.91  thf('78', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 1.64/1.91      inference('sup-', [status(thm)], ['56', '59'])).
% 1.64/1.91  thf('79', plain,
% 1.64/1.91      (((((sk_A) = (k1_xboole_0))
% 1.64/1.91         | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91         | ((sk_C_1) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('demod', [status(thm)], ['77', '78'])).
% 1.64/1.91  thf('80', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('81', plain,
% 1.64/1.91      (![X26 : $i, X27 : $i]:
% 1.64/1.91         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.64/1.91  thf('82', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 1.64/1.91      inference('sup-', [status(thm)], ['80', '81'])).
% 1.64/1.91  thf('83', plain,
% 1.64/1.91      (![X15 : $i, X16 : $i]:
% 1.64/1.91         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.64/1.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.64/1.91  thf('84', plain, (((k3_xboole_0 @ sk_F @ sk_C_1) = (sk_F))),
% 1.64/1.91      inference('sup-', [status(thm)], ['82', '83'])).
% 1.64/1.91  thf('85', plain,
% 1.64/1.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.64/1.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.64/1.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.64/1.91  thf('86', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X0 @ sk_F) | ~ (r1_xboole_0 @ sk_F @ sk_C_1))),
% 1.64/1.91      inference('sup-', [status(thm)], ['84', '85'])).
% 1.64/1.91  thf('87', plain,
% 1.64/1.91      ((![X0 : $i]:
% 1.64/1.91          (~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 1.64/1.91           | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91           | ((sk_A) = (k1_xboole_0))
% 1.64/1.91           | ~ (r2_hidden @ X0 @ sk_F)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['79', '86'])).
% 1.64/1.91  thf('88', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('89', plain,
% 1.64/1.91      ((![X0 : $i]:
% 1.64/1.91          (((sk_B_2) = (k1_xboole_0))
% 1.64/1.91           | ((sk_A) = (k1_xboole_0))
% 1.64/1.91           | ~ (r2_hidden @ X0 @ sk_F)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('demod', [status(thm)], ['87', '88'])).
% 1.64/1.91  thf('90', plain,
% 1.64/1.91      (((((sk_A) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['72', '89'])).
% 1.64/1.91  thf('91', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B_2))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('92', plain,
% 1.64/1.91      (![X26 : $i, X27 : $i]:
% 1.64/1.91         ((r1_tarski @ X26 @ X27) | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t3_subset])).
% 1.64/1.91  thf('93', plain, ((r1_tarski @ sk_E @ sk_B_2)),
% 1.64/1.91      inference('sup-', [status(thm)], ['91', '92'])).
% 1.64/1.91  thf('94', plain,
% 1.64/1.91      (![X15 : $i, X16 : $i]:
% 1.64/1.91         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.64/1.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.64/1.91  thf('95', plain, (((k3_xboole_0 @ sk_E @ sk_B_2) = (sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['93', '94'])).
% 1.64/1.91  thf('96', plain,
% 1.64/1.91      (((((k3_xboole_0 @ sk_E @ k1_xboole_0) = (sk_E))
% 1.64/1.91         | ((sk_A) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup+', [status(thm)], ['90', '95'])).
% 1.64/1.91  thf('97', plain,
% 1.64/1.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['32', '33'])).
% 1.64/1.91  thf('98', plain,
% 1.64/1.91      (((((k1_xboole_0) = (sk_E)) | ((sk_A) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('demod', [status(thm)], ['96', '97'])).
% 1.64/1.91  thf('99', plain, (((v1_xboole_0 @ sk_D) | ~ (v1_xboole_0 @ sk_A))),
% 1.64/1.91      inference('sup+', [status(thm)], ['9', '16'])).
% 1.64/1.91  thf('100', plain,
% 1.64/1.91      (((~ (v1_xboole_0 @ k1_xboole_0)
% 1.64/1.91         | ((k1_xboole_0) = (sk_E))
% 1.64/1.91         | (v1_xboole_0 @ sk_D)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['98', '99'])).
% 1.64/1.91  thf('101', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('102', plain,
% 1.64/1.91      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf(d10_xboole_0, axiom,
% 1.64/1.91    (![A:$i,B:$i]:
% 1.64/1.91     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.64/1.91  thf('103', plain,
% 1.64/1.91      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 1.64/1.91      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.64/1.91  thf('104', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 1.64/1.91      inference('simplify', [status(thm)], ['103'])).
% 1.64/1.91  thf('105', plain,
% 1.64/1.91      (![X15 : $i, X16 : $i]:
% 1.64/1.91         (((k3_xboole_0 @ X15 @ X16) = (X15)) | ~ (r1_tarski @ X15 @ X16))),
% 1.64/1.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.64/1.91  thf('106', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['104', '105'])).
% 1.64/1.91  thf('107', plain,
% 1.64/1.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.64/1.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.64/1.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.64/1.91  thf('108', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['106', '107'])).
% 1.64/1.91  thf('109', plain,
% 1.64/1.91      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['102', '108'])).
% 1.64/1.91  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.91      inference('sup-', [status(thm)], ['101', '109'])).
% 1.64/1.91  thf('111', plain,
% 1.64/1.91      (((((k1_xboole_0) = (sk_E)) | (v1_xboole_0 @ sk_D)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('demod', [status(thm)], ['100', '110'])).
% 1.64/1.91  thf('112', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.64/1.91      inference('sup-', [status(thm)], ['25', '46'])).
% 1.64/1.91  thf('113', plain,
% 1.64/1.91      ((((k1_xboole_0) = (sk_E)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['111', '112'])).
% 1.64/1.91  thf('114', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['26', '45'])).
% 1.64/1.91  thf('115', plain,
% 1.64/1.91      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ k1_xboole_0)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['113', '114'])).
% 1.64/1.91  thf('116', plain,
% 1.64/1.91      ((![X0 : $i]:
% 1.64/1.91          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_D @ X0)) | ~ (v1_xboole_0 @ X0)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['71', '115'])).
% 1.64/1.91  thf('117', plain,
% 1.64/1.91      ((~ (v1_xboole_0 @ k1_xboole_0))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['70', '116'])).
% 1.64/1.91  thf('118', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.91      inference('sup-', [status(thm)], ['101', '109'])).
% 1.64/1.91  thf('119', plain,
% 1.64/1.91      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F))),
% 1.64/1.91      inference('demod', [status(thm)], ['117', '118'])).
% 1.64/1.91  thf('120', plain,
% 1.64/1.91      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['49', '52'])).
% 1.64/1.91  thf('121', plain,
% 1.64/1.91      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.91         ((r2_hidden @ (k1_mcart_1 @ X32) @ X33)
% 1.64/1.91          | ~ (r2_hidden @ X32 @ (k2_zfmisc_1 @ X33 @ X34)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t10_mcart_1])).
% 1.64/1.91  thf('122', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 1.64/1.91      inference('sup-', [status(thm)], ['120', '121'])).
% 1.64/1.91  thf('123', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 1.64/1.91      inference('sup-', [status(thm)], ['56', '59'])).
% 1.64/1.91  thf('124', plain,
% 1.64/1.91      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('125', plain,
% 1.64/1.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.64/1.91         (((X35) = (k1_xboole_0))
% 1.64/1.91          | ((X36) = (k1_xboole_0))
% 1.64/1.91          | ((k5_mcart_1 @ X35 @ X36 @ X38 @ X37)
% 1.64/1.91              = (k1_mcart_1 @ (k1_mcart_1 @ X37)))
% 1.64/1.91          | ~ (m1_subset_1 @ X37 @ (k3_zfmisc_1 @ X35 @ X36 @ X38))
% 1.64/1.91          | ((X38) = (k1_xboole_0)))),
% 1.64/1.91      inference('cnf', [status(esa)], [t50_mcart_1])).
% 1.64/1.91  thf('126', plain,
% 1.64/1.91      ((((sk_C_1) = (k1_xboole_0))
% 1.64/1.91        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G)
% 1.64/1.91            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 1.64/1.91        | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91        | ((sk_A) = (k1_xboole_0)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['124', '125'])).
% 1.64/1.91  thf('127', plain,
% 1.64/1.91      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('split', [status(esa)], ['64'])).
% 1.64/1.91  thf('128', plain,
% 1.64/1.91      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 1.64/1.91         | ((sk_A) = (k1_xboole_0))
% 1.64/1.91         | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91         | ((sk_C_1) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['126', '127'])).
% 1.64/1.91  thf('129', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 1.64/1.91      inference('sup-', [status(thm)], ['120', '121'])).
% 1.64/1.91  thf('130', plain,
% 1.64/1.91      (((((sk_A) = (k1_xboole_0))
% 1.64/1.91         | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91         | ((sk_C_1) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('demod', [status(thm)], ['128', '129'])).
% 1.64/1.91  thf('131', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X0 @ sk_F) | ~ (r1_xboole_0 @ sk_F @ sk_C_1))),
% 1.64/1.91      inference('sup-', [status(thm)], ['84', '85'])).
% 1.64/1.91  thf('132', plain,
% 1.64/1.91      ((![X0 : $i]:
% 1.64/1.91          (~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 1.64/1.91           | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91           | ((sk_A) = (k1_xboole_0))
% 1.64/1.91           | ~ (r2_hidden @ X0 @ sk_F)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['130', '131'])).
% 1.64/1.91  thf('133', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('134', plain,
% 1.64/1.91      ((![X0 : $i]:
% 1.64/1.91          (((sk_B_2) = (k1_xboole_0))
% 1.64/1.91           | ((sk_A) = (k1_xboole_0))
% 1.64/1.91           | ~ (r2_hidden @ X0 @ sk_F)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('demod', [status(thm)], ['132', '133'])).
% 1.64/1.91  thf('135', plain,
% 1.64/1.91      (((((sk_A) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['123', '134'])).
% 1.64/1.91  thf('136', plain, (((k3_xboole_0 @ sk_E @ sk_B_2) = (sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['93', '94'])).
% 1.64/1.91  thf('137', plain,
% 1.64/1.91      (((((k3_xboole_0 @ sk_E @ k1_xboole_0) = (sk_E))
% 1.64/1.91         | ((sk_A) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup+', [status(thm)], ['135', '136'])).
% 1.64/1.91  thf('138', plain,
% 1.64/1.91      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['32', '33'])).
% 1.64/1.91  thf('139', plain,
% 1.64/1.91      (((((k1_xboole_0) = (sk_E)) | ((sk_A) = (k1_xboole_0))))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('demod', [status(thm)], ['137', '138'])).
% 1.64/1.91  thf('140', plain, (((k3_xboole_0 @ sk_D @ sk_A) = (sk_D))),
% 1.64/1.91      inference('sup-', [status(thm)], ['7', '8'])).
% 1.64/1.91  thf('141', plain,
% 1.64/1.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.64/1.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.64/1.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.64/1.91  thf('142', plain,
% 1.64/1.91      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_D) | ~ (r1_xboole_0 @ sk_D @ sk_A))),
% 1.64/1.91      inference('sup-', [status(thm)], ['140', '141'])).
% 1.64/1.91  thf('143', plain,
% 1.64/1.91      ((![X0 : $i]:
% 1.64/1.91          (~ (r1_xboole_0 @ sk_D @ k1_xboole_0)
% 1.64/1.91           | ((k1_xboole_0) = (sk_E))
% 1.64/1.91           | ~ (r2_hidden @ X0 @ sk_D)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['139', '142'])).
% 1.64/1.91  thf('144', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('145', plain,
% 1.64/1.91      ((![X0 : $i]: (((k1_xboole_0) = (sk_E)) | ~ (r2_hidden @ X0 @ sk_D)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('demod', [status(thm)], ['143', '144'])).
% 1.64/1.91  thf('146', plain,
% 1.64/1.91      ((((k1_xboole_0) = (sk_E)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['122', '145'])).
% 1.64/1.91  thf('147', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.64/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.91  thf('148', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.64/1.91      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.64/1.91  thf('149', plain, (~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 1.64/1.91      inference('sup-', [status(thm)], ['147', '148'])).
% 1.64/1.91  thf('150', plain,
% 1.64/1.91      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_D @ k1_xboole_0 @ sk_F)))
% 1.64/1.91         <= (~
% 1.64/1.91             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['146', '149'])).
% 1.64/1.91  thf('151', plain,
% 1.64/1.91      (![X0 : $i]: (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['68', '69'])).
% 1.64/1.91  thf('152', plain,
% 1.64/1.91      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['0', '1'])).
% 1.64/1.91  thf('153', plain,
% 1.64/1.91      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['151', '152'])).
% 1.64/1.91  thf('154', plain,
% 1.64/1.91      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.64/1.91         ((k3_zfmisc_1 @ X29 @ X30 @ X31)
% 1.64/1.91           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30) @ X31))),
% 1.64/1.91      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 1.64/1.91  thf('155', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0)
% 1.64/1.91           = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 1.64/1.91      inference('sup+', [status(thm)], ['153', '154'])).
% 1.64/1.91  thf('156', plain,
% 1.64/1.91      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['39', '40'])).
% 1.64/1.91  thf('157', plain,
% 1.64/1.91      (![X0 : $i, X1 : $i]:
% 1.64/1.91         ((k3_zfmisc_1 @ X1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.64/1.91      inference('demod', [status(thm)], ['155', '156'])).
% 1.64/1.91  thf('158', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.91      inference('sup-', [status(thm)], ['101', '109'])).
% 1.64/1.91  thf('159', plain,
% 1.64/1.91      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D))),
% 1.64/1.91      inference('demod', [status(thm)], ['150', '157', '158'])).
% 1.64/1.91  thf('160', plain,
% 1.64/1.91      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_E)) | 
% 1.64/1.91       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_D)) | 
% 1.64/1.91       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_F))),
% 1.64/1.91      inference('split', [status(esa)], ['64'])).
% 1.64/1.91  thf('161', plain,
% 1.64/1.91      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_E))),
% 1.64/1.91      inference('sat_resolution*', [status(thm)], ['119', '159', '160'])).
% 1.64/1.91  thf('162', plain,
% 1.64/1.91      (~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_G) @ sk_E)),
% 1.64/1.91      inference('simpl_trail', [status(thm)], ['65', '161'])).
% 1.64/1.91  thf('163', plain,
% 1.64/1.91      ((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 1.64/1.91        | ((sk_A) = (k1_xboole_0))
% 1.64/1.91        | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91        | ((sk_C_1) = (k1_xboole_0)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['63', '162'])).
% 1.64/1.91  thf('164', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 1.64/1.91      inference('sup-', [status(thm)], ['53', '54'])).
% 1.64/1.91  thf('165', plain,
% 1.64/1.91      ((((sk_A) = (k1_xboole_0))
% 1.64/1.91        | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91        | ((sk_C_1) = (k1_xboole_0)))),
% 1.64/1.91      inference('demod', [status(thm)], ['163', '164'])).
% 1.64/1.91  thf('166', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X0 @ sk_F) | ~ (r1_xboole_0 @ sk_F @ sk_C_1))),
% 1.64/1.91      inference('sup-', [status(thm)], ['84', '85'])).
% 1.64/1.91  thf('167', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (r1_xboole_0 @ sk_F @ k1_xboole_0)
% 1.64/1.91          | ((sk_B_2) = (k1_xboole_0))
% 1.64/1.91          | ((sk_A) = (k1_xboole_0))
% 1.64/1.91          | ~ (r2_hidden @ X0 @ sk_F))),
% 1.64/1.91      inference('sup-', [status(thm)], ['165', '166'])).
% 1.64/1.91  thf('168', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('169', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (((sk_B_2) = (k1_xboole_0))
% 1.64/1.91          | ((sk_A) = (k1_xboole_0))
% 1.64/1.91          | ~ (r2_hidden @ X0 @ sk_F))),
% 1.64/1.91      inference('demod', [status(thm)], ['167', '168'])).
% 1.64/1.91  thf('170', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 1.64/1.91      inference('sup-', [status(thm)], ['60', '169'])).
% 1.64/1.91  thf('171', plain, (((k3_xboole_0 @ sk_E @ sk_B_2) = (sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['93', '94'])).
% 1.64/1.91  thf('172', plain,
% 1.64/1.91      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 1.64/1.91          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.64/1.91      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.64/1.91  thf('173', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (r2_hidden @ X0 @ sk_E) | ~ (r1_xboole_0 @ sk_E @ sk_B_2))),
% 1.64/1.91      inference('sup-', [status(thm)], ['171', '172'])).
% 1.64/1.91  thf('174', plain,
% 1.64/1.91      (![X0 : $i]:
% 1.64/1.91         (~ (r1_xboole_0 @ sk_E @ k1_xboole_0)
% 1.64/1.91          | ((sk_A) = (k1_xboole_0))
% 1.64/1.91          | ~ (r2_hidden @ X0 @ sk_E))),
% 1.64/1.91      inference('sup-', [status(thm)], ['170', '173'])).
% 1.64/1.91  thf('175', plain, (![X20 : $i]: (r1_xboole_0 @ X20 @ k1_xboole_0)),
% 1.64/1.91      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.64/1.91  thf('176', plain,
% 1.64/1.91      (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ X0 @ sk_E))),
% 1.64/1.91      inference('demod', [status(thm)], ['174', '175'])).
% 1.64/1.91  thf('177', plain, (((sk_A) = (k1_xboole_0))),
% 1.64/1.91      inference('sup-', [status(thm)], ['55', '176'])).
% 1.64/1.91  thf('178', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.91      inference('sup-', [status(thm)], ['101', '109'])).
% 1.64/1.91  thf('179', plain, ($false),
% 1.64/1.91      inference('demod', [status(thm)], ['48', '177', '178'])).
% 1.64/1.91  
% 1.64/1.91  % SZS output end Refutation
% 1.64/1.91  
% 1.76/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
