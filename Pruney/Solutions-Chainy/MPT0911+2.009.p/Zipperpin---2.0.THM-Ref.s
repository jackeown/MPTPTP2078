%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AsBzdlzwie

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:57 EST 2020

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 433 expanded)
%              Number of leaves         :   35 ( 143 expanded)
%              Depth                    :   23
%              Number of atoms          : 1164 (7603 expanded)
%              Number of equality atoms :  115 ( 954 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X14 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t24_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33
        = ( k4_tarski @ ( k1_mcart_1 @ X33 ) @ ( k2_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k2_zfmisc_1 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ( X3
        = ( k4_tarski @ ( k1_mcart_1 @ X3 ) @ ( k2_mcart_1 @ X3 ) ) )
      | ( ( k2_zfmisc_1 @ X2 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('20',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33
        = ( k4_tarski @ ( k1_mcart_1 @ X33 ) @ ( k2_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k2_zfmisc_1 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('30',plain,
    ( ( ( k1_mcart_1 @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k3_mcart_1 @ X15 @ X16 @ X17 )
      = ( k4_tarski @ ( k4_tarski @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X0 )
        = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('34',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X29 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('37',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 )
    | ( v1_xboole_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ X12 @ X13 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ sk_B_2 )
      | ( sk_E
       != ( k3_mcart_1 @ X45 @ X44 @ X46 ) )
      | ( sk_D = X46 )
      | ~ ( m1_subset_1 @ X46 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X45 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C_1 )
      | ( sk_D = X1 )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( m1_subset_1 @ ( k5_mcart_1 @ X21 @ X22 @ X23 @ X24 ) @ X21 )
      | ~ ( m1_subset_1 @ X24 @ ( k3_zfmisc_1 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_mcart_1])).

thf('45',plain,(
    m1_subset_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
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

thf('47',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X40 @ X41 @ X43 @ X42 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X42 ) ) )
      | ~ ( m1_subset_1 @ X42 @ ( k3_zfmisc_1 @ X40 @ X41 @ X43 ) )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('48',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['48','49','50','51'])).

thf('53',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference(demod,[status(thm)],['45','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) )
      | ( v1_xboole_0 @ sk_E )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_E ) ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_C_1 )
      | ( sk_D = X0 )
      | ( v1_xboole_0 @ sk_E )
      | ( sk_E
       != ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X25 @ X26 @ X27 @ X28 ) @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X25 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('59',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X40 @ X41 @ X43 @ X42 )
        = ( k2_mcart_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k3_zfmisc_1 @ X40 @ X41 @ X43 ) )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('62',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['59','66'])).

thf('68',plain,
    ( ( sk_E != sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_E )
    | ( sk_D
      = ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['56','67'])).

thf('69',plain,
    ( ( sk_D
      = ( k2_mcart_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['62','63','64','65'])).

thf('72',plain,(
    sk_D
 != ( k2_mcart_1 @ sk_E ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( sk_E
      = ( k4_tarski @ ( k1_mcart_1 @ sk_E ) @ ( k2_mcart_1 @ sk_E ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(fc1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) )).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('76',plain,
    ( ~ ( v1_xboole_0 @ sk_E )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','76'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('78',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('79',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('82',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('83',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','77','85'])).

thf('87',plain,(
    v1_xboole_0 @ sk_E ),
    inference(demod,[status(thm)],['2','86'])).

thf('88',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['73','76'])).

thf('89',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ( m1_subset_1 @ X14 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('90',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( X33
        = ( k4_tarski @ ( k1_mcart_1 @ X33 ) @ ( k2_mcart_1 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k2_zfmisc_1 @ X32 @ X34 ) )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t24_mcart_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X0 = k1_xboole_0 )
      | ( X2
        = ( k4_tarski @ ( k1_mcart_1 @ X2 ) @ ( k2_mcart_1 @ X2 ) ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['81','84'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) )
      | ( sk_B_2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k4_tarski @ ( k1_mcart_1 @ X0 ) @ ( k2_mcart_1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['94','95','96'])).

thf('98',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( v1_xboole_0 @ ( k4_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc1_zfmisc_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    $false ),
    inference('sup-',[status(thm)],['87','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AsBzdlzwie
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.43/2.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.43/2.61  % Solved by: fo/fo7.sh
% 2.43/2.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.43/2.61  % done 2366 iterations in 2.149s
% 2.43/2.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.43/2.61  % SZS output start Refutation
% 2.43/2.61  thf(sk_E_type, type, sk_E: $i).
% 2.43/2.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.43/2.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.43/2.61  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 2.43/2.61  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 2.43/2.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.43/2.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.43/2.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.43/2.61  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 2.43/2.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.43/2.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.43/2.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.43/2.61  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 2.43/2.61  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 2.43/2.61  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 2.43/2.61  thf(sk_A_type, type, sk_A: $i).
% 2.43/2.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 2.43/2.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.43/2.61  thf(sk_D_type, type, sk_D: $i).
% 2.43/2.61  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 2.43/2.61  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.43/2.61  thf(t71_mcart_1, conjecture,
% 2.43/2.61    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.43/2.61     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61       ( ( ![F:$i]:
% 2.43/2.61           ( ( m1_subset_1 @ F @ A ) =>
% 2.43/2.61             ( ![G:$i]:
% 2.43/2.61               ( ( m1_subset_1 @ G @ B ) =>
% 2.43/2.61                 ( ![H:$i]:
% 2.43/2.61                   ( ( m1_subset_1 @ H @ C ) =>
% 2.43/2.61                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 2.43/2.61                       ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 2.43/2.61         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.43/2.61           ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.43/2.61           ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 2.43/2.61  thf(zf_stmt_0, negated_conjecture,
% 2.43/2.61    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 2.43/2.61        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61          ( ( ![F:$i]:
% 2.43/2.61              ( ( m1_subset_1 @ F @ A ) =>
% 2.43/2.61                ( ![G:$i]:
% 2.43/2.61                  ( ( m1_subset_1 @ G @ B ) =>
% 2.43/2.61                    ( ![H:$i]:
% 2.43/2.61                      ( ( m1_subset_1 @ H @ C ) =>
% 2.43/2.61                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 2.43/2.61                          ( ( D ) = ( H ) ) ) ) ) ) ) ) ) =>
% 2.43/2.61            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.43/2.61              ( ( C ) = ( k1_xboole_0 ) ) | 
% 2.43/2.61              ( ( D ) = ( k7_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 2.43/2.61    inference('cnf.neg', [status(esa)], [t71_mcart_1])).
% 2.43/2.61  thf('0', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(d2_subset_1, axiom,
% 2.43/2.61    (![A:$i,B:$i]:
% 2.43/2.61     ( ( ( v1_xboole_0 @ A ) =>
% 2.43/2.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.43/2.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.43/2.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.43/2.61  thf('1', plain,
% 2.43/2.61      (![X13 : $i, X14 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X14 @ X13)
% 2.43/2.61          | (v1_xboole_0 @ X14)
% 2.43/2.61          | ~ (v1_xboole_0 @ X13))),
% 2.43/2.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.43/2.61  thf('2', plain,
% 2.43/2.61      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup-', [status(thm)], ['0', '1'])).
% 2.43/2.61  thf('3', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('4', plain,
% 2.43/2.61      (![X12 : $i, X13 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X12 @ X13)
% 2.43/2.61          | (r2_hidden @ X12 @ X13)
% 2.43/2.61          | (v1_xboole_0 @ X13))),
% 2.43/2.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.43/2.61  thf('5', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['3', '4'])).
% 2.43/2.61  thf(d3_zfmisc_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i]:
% 2.43/2.61     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 2.43/2.61       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 2.43/2.61  thf('6', plain,
% 2.43/2.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.43/2.61         ((k3_zfmisc_1 @ X18 @ X19 @ X20)
% 2.43/2.61           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19) @ X20))),
% 2.43/2.61      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.43/2.61  thf(t10_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i]:
% 2.43/2.61     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 2.43/2.61       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 2.43/2.61         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 2.43/2.61  thf('7', plain,
% 2.43/2.61      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.43/2.61         ((r2_hidden @ (k1_mcart_1 @ X29) @ X30)
% 2.43/2.61          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.43/2.61  thf('8', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.43/2.61         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.43/2.61          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['6', '7'])).
% 2.43/2.61  thf('9', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['5', '8'])).
% 2.43/2.61  thf(d1_xboole_0, axiom,
% 2.43/2.61    (![A:$i]:
% 2.43/2.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.43/2.61  thf('10', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.43/2.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.43/2.61  thf('11', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['9', '10'])).
% 2.43/2.61  thf('12', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('13', plain,
% 2.43/2.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.43/2.61         ((k3_zfmisc_1 @ X18 @ X19 @ X20)
% 2.43/2.61           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19) @ X20))),
% 2.43/2.61      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 2.43/2.61  thf(t24_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i]:
% 2.43/2.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.43/2.61          ( ~( ![C:$i]:
% 2.43/2.61               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 2.43/2.61                 ( ( C ) =
% 2.43/2.61                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 2.43/2.61  thf('14', plain,
% 2.43/2.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.43/2.61         (((X32) = (k1_xboole_0))
% 2.43/2.61          | ((X33) = (k4_tarski @ (k1_mcart_1 @ X33) @ (k2_mcart_1 @ X33)))
% 2.43/2.61          | ~ (m1_subset_1 @ X33 @ (k2_zfmisc_1 @ X32 @ X34))
% 2.43/2.61          | ((X34) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t24_mcart_1])).
% 2.43/2.61  thf('15', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 2.43/2.61          | ((X0) = (k1_xboole_0))
% 2.43/2.61          | ((X3) = (k4_tarski @ (k1_mcart_1 @ X3) @ (k2_mcart_1 @ X3)))
% 2.43/2.61          | ((k2_zfmisc_1 @ X2 @ X1) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['13', '14'])).
% 2.43/2.61  thf('16', plain,
% 2.43/2.61      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E)))
% 2.43/2.61        | ((sk_C_1) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['12', '15'])).
% 2.43/2.61  thf('17', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('18', plain,
% 2.43/2.61      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.43/2.61  thf('19', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['5', '8'])).
% 2.43/2.61  thf('20', plain,
% 2.43/2.61      (![X12 : $i, X13 : $i]:
% 2.43/2.61         (~ (r2_hidden @ X12 @ X13)
% 2.43/2.61          | (m1_subset_1 @ X12 @ X13)
% 2.43/2.61          | (v1_xboole_0 @ X13))),
% 2.43/2.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.43/2.61  thf('21', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.43/2.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.43/2.61  thf('22', plain,
% 2.43/2.61      (![X12 : $i, X13 : $i]:
% 2.43/2.61         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 2.43/2.61      inference('clc', [status(thm)], ['20', '21'])).
% 2.43/2.61  thf('23', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (m1_subset_1 @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['19', '22'])).
% 2.43/2.61  thf('24', plain,
% 2.43/2.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.43/2.61         (((X32) = (k1_xboole_0))
% 2.43/2.61          | ((X33) = (k4_tarski @ (k1_mcart_1 @ X33) @ (k2_mcart_1 @ X33)))
% 2.43/2.61          | ~ (m1_subset_1 @ X33 @ (k2_zfmisc_1 @ X32 @ X34))
% 2.43/2.61          | ((X34) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t24_mcart_1])).
% 2.43/2.61  thf('25', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((k1_mcart_1 @ sk_E)
% 2.43/2.61            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 2.43/2.61               (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['23', '24'])).
% 2.43/2.61  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('27', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('28', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | ((k1_mcart_1 @ sk_E)
% 2.43/2.61            = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 2.43/2.61               (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['25', '26', '27'])).
% 2.43/2.61  thf('29', plain,
% 2.43/2.61      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup-', [status(thm)], ['0', '1'])).
% 2.43/2.61  thf('30', plain,
% 2.43/2.61      ((((k1_mcart_1 @ sk_E)
% 2.43/2.61          = (k4_tarski @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 2.43/2.61             (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))
% 2.43/2.61        | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup-', [status(thm)], ['28', '29'])).
% 2.43/2.61  thf(d3_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i]:
% 2.43/2.61     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 2.43/2.61  thf('31', plain,
% 2.43/2.61      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.43/2.61         ((k3_mcart_1 @ X15 @ X16 @ X17)
% 2.43/2.61           = (k4_tarski @ (k4_tarski @ X15 @ X16) @ X17))),
% 2.43/2.61      inference('cnf', [status(esa)], [d3_mcart_1])).
% 2.43/2.61  thf('32', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 2.43/2.61            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X0)
% 2.43/2.61            = (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 2.43/2.61          | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup+', [status(thm)], ['30', '31'])).
% 2.43/2.61  thf('33', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['5', '8'])).
% 2.43/2.61  thf('34', plain,
% 2.43/2.61      (![X29 : $i, X30 : $i, X31 : $i]:
% 2.43/2.61         ((r2_hidden @ (k2_mcart_1 @ X29) @ X31)
% 2.43/2.61          | ~ (r2_hidden @ X29 @ (k2_zfmisc_1 @ X30 @ X31)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t10_mcart_1])).
% 2.43/2.61  thf('35', plain,
% 2.43/2.61      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 2.43/2.61      inference('sup-', [status(thm)], ['33', '34'])).
% 2.43/2.61  thf('36', plain,
% 2.43/2.61      ((~ (v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))
% 2.43/2.61        | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup-', [status(thm)], ['0', '1'])).
% 2.43/2.61  thf('37', plain,
% 2.43/2.61      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2)
% 2.43/2.61        | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup-', [status(thm)], ['35', '36'])).
% 2.43/2.61  thf('38', plain,
% 2.43/2.61      (![X12 : $i, X13 : $i]:
% 2.43/2.61         ((m1_subset_1 @ X12 @ X13) | ~ (r2_hidden @ X12 @ X13))),
% 2.43/2.61      inference('clc', [status(thm)], ['20', '21'])).
% 2.43/2.61  thf('39', plain,
% 2.43/2.61      (((v1_xboole_0 @ sk_E)
% 2.43/2.61        | (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B_2))),
% 2.43/2.61      inference('sup-', [status(thm)], ['37', '38'])).
% 2.43/2.61  thf('40', plain,
% 2.43/2.61      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X44 @ sk_B_2)
% 2.43/2.61          | ((sk_E) != (k3_mcart_1 @ X45 @ X44 @ X46))
% 2.43/2.61          | ((sk_D) = (X46))
% 2.43/2.61          | ~ (m1_subset_1 @ X46 @ sk_C_1)
% 2.43/2.61          | ~ (m1_subset_1 @ X45 @ sk_A))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('41', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i]:
% 2.43/2.61         ((v1_xboole_0 @ sk_E)
% 2.43/2.61          | ~ (m1_subset_1 @ X0 @ sk_A)
% 2.43/2.61          | ~ (m1_subset_1 @ X1 @ sk_C_1)
% 2.43/2.61          | ((sk_D) = (X1))
% 2.43/2.61          | ((sk_E)
% 2.43/2.61              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['39', '40'])).
% 2.43/2.61  thf('42', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 2.43/2.61          | (v1_xboole_0 @ sk_E)
% 2.43/2.61          | ((sk_D) = (X0))
% 2.43/2.61          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 2.43/2.61          | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 2.43/2.61          | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('sup-', [status(thm)], ['32', '41'])).
% 2.43/2.61  thf('43', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(dt_k5_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.43/2.61     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61       ( m1_subset_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ A ) ))).
% 2.43/2.61  thf('44', plain,
% 2.43/2.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.43/2.61         ((m1_subset_1 @ (k5_mcart_1 @ X21 @ X22 @ X23 @ X24) @ X21)
% 2.43/2.61          | ~ (m1_subset_1 @ X24 @ (k3_zfmisc_1 @ X21 @ X22 @ X23)))),
% 2.43/2.61      inference('cnf', [status(esa)], [dt_k5_mcart_1])).
% 2.43/2.61  thf('45', plain,
% 2.43/2.61      ((m1_subset_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E) @ sk_A)),
% 2.43/2.61      inference('sup-', [status(thm)], ['43', '44'])).
% 2.43/2.61  thf('46', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(t50_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i]:
% 2.43/2.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 2.43/2.61          ( ( C ) != ( k1_xboole_0 ) ) & 
% 2.43/2.61          ( ~( ![D:$i]:
% 2.43/2.61               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 2.43/2.61                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.43/2.61                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 2.43/2.61                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 2.43/2.61                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 2.43/2.61  thf('47', plain,
% 2.43/2.61      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.43/2.61         (((X40) = (k1_xboole_0))
% 2.43/2.61          | ((X41) = (k1_xboole_0))
% 2.43/2.61          | ((k5_mcart_1 @ X40 @ X41 @ X43 @ X42)
% 2.43/2.61              = (k1_mcart_1 @ (k1_mcart_1 @ X42)))
% 2.43/2.61          | ~ (m1_subset_1 @ X42 @ (k3_zfmisc_1 @ X40 @ X41 @ X43))
% 2.43/2.61          | ((X43) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.43/2.61  thf('48', plain,
% 2.43/2.61      ((((sk_C_1) = (k1_xboole_0))
% 2.43/2.61        | ((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E)
% 2.43/2.61            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['46', '47'])).
% 2.43/2.61  thf('49', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('50', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('51', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('52', plain,
% 2.43/2.61      (((k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E)
% 2.43/2.61         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['48', '49', '50', '51'])).
% 2.43/2.61  thf('53', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 2.43/2.61      inference('demod', [status(thm)], ['45', '52'])).
% 2.43/2.61  thf('54', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0))
% 2.43/2.61          | (v1_xboole_0 @ sk_E)
% 2.43/2.61          | ((sk_D) = (X0))
% 2.43/2.61          | ~ (m1_subset_1 @ X0 @ sk_C_1)
% 2.43/2.61          | (v1_xboole_0 @ sk_E))),
% 2.43/2.61      inference('demod', [status(thm)], ['42', '53'])).
% 2.43/2.61  thf('55', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (~ (m1_subset_1 @ X0 @ sk_C_1)
% 2.43/2.61          | ((sk_D) = (X0))
% 2.43/2.61          | (v1_xboole_0 @ sk_E)
% 2.43/2.61          | ((sk_E) != (k4_tarski @ (k1_mcart_1 @ sk_E) @ X0)))),
% 2.43/2.61      inference('simplify', [status(thm)], ['54'])).
% 2.43/2.61  thf('56', plain,
% 2.43/2.61      ((((sk_E) != (sk_E))
% 2.43/2.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | (v1_xboole_0 @ sk_E)
% 2.43/2.61        | ((sk_D) = (k2_mcart_1 @ sk_E))
% 2.43/2.61        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1))),
% 2.43/2.61      inference('sup-', [status(thm)], ['18', '55'])).
% 2.43/2.61  thf('57', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf(dt_k7_mcart_1, axiom,
% 2.43/2.61    (![A:$i,B:$i,C:$i,D:$i]:
% 2.43/2.61     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 2.43/2.61       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 2.43/2.61  thf('58', plain,
% 2.43/2.61      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.43/2.61         ((m1_subset_1 @ (k7_mcart_1 @ X25 @ X26 @ X27 @ X28) @ X27)
% 2.43/2.61          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X25 @ X26 @ X27)))),
% 2.43/2.61      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 2.43/2.61  thf('59', plain,
% 2.43/2.61      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 2.43/2.61      inference('sup-', [status(thm)], ['57', '58'])).
% 2.43/2.61  thf('60', plain,
% 2.43/2.61      ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('61', plain,
% 2.43/2.61      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 2.43/2.61         (((X40) = (k1_xboole_0))
% 2.43/2.61          | ((X41) = (k1_xboole_0))
% 2.43/2.61          | ((k7_mcart_1 @ X40 @ X41 @ X43 @ X42) = (k2_mcart_1 @ X42))
% 2.43/2.61          | ~ (m1_subset_1 @ X42 @ (k3_zfmisc_1 @ X40 @ X41 @ X43))
% 2.43/2.61          | ((X43) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t50_mcart_1])).
% 2.43/2.61  thf('62', plain,
% 2.43/2.61      ((((sk_C_1) = (k1_xboole_0))
% 2.43/2.61        | ((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E) = (k2_mcart_1 @ sk_E))
% 2.43/2.61        | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_A) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['60', '61'])).
% 2.43/2.61  thf('63', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('64', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('65', plain, (((sk_C_1) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('66', plain,
% 2.43/2.61      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E) = (k2_mcart_1 @ sk_E))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['62', '63', '64', '65'])).
% 2.43/2.61  thf('67', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C_1)),
% 2.43/2.61      inference('demod', [status(thm)], ['59', '66'])).
% 2.43/2.61  thf('68', plain,
% 2.43/2.61      ((((sk_E) != (sk_E))
% 2.43/2.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | (v1_xboole_0 @ sk_E)
% 2.43/2.61        | ((sk_D) = (k2_mcart_1 @ sk_E)))),
% 2.43/2.61      inference('demod', [status(thm)], ['56', '67'])).
% 2.43/2.61  thf('69', plain,
% 2.43/2.61      ((((sk_D) = (k2_mcart_1 @ sk_E))
% 2.43/2.61        | (v1_xboole_0 @ sk_E)
% 2.43/2.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.43/2.61      inference('simplify', [status(thm)], ['68'])).
% 2.43/2.61  thf('70', plain, (((sk_D) != (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('71', plain,
% 2.43/2.61      (((k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_E) = (k2_mcart_1 @ sk_E))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['62', '63', '64', '65'])).
% 2.43/2.61  thf('72', plain, (((sk_D) != (k2_mcart_1 @ sk_E))),
% 2.43/2.61      inference('demod', [status(thm)], ['70', '71'])).
% 2.43/2.61  thf('73', plain,
% 2.43/2.61      (((v1_xboole_0 @ sk_E) | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['69', '72'])).
% 2.43/2.61  thf('74', plain,
% 2.43/2.61      ((((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 2.43/2.61        | ((sk_E) = (k4_tarski @ (k1_mcart_1 @ sk_E) @ (k2_mcart_1 @ sk_E))))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 2.43/2.61  thf(fc1_zfmisc_1, axiom,
% 2.43/2.61    (![A:$i,B:$i]: ( ~( v1_xboole_0 @ ( k4_tarski @ A @ B ) ) ))).
% 2.43/2.61  thf('75', plain,
% 2.43/2.61      (![X10 : $i, X11 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X10 @ X11))),
% 2.43/2.61      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 2.43/2.61  thf('76', plain,
% 2.43/2.61      ((~ (v1_xboole_0 @ sk_E)
% 2.43/2.61        | ((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['74', '75'])).
% 2.43/2.61  thf('77', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 2.43/2.61      inference('clc', [status(thm)], ['73', '76'])).
% 2.43/2.61  thf(d3_tarski, axiom,
% 2.43/2.61    (![A:$i,B:$i]:
% 2.43/2.61     ( ( r1_tarski @ A @ B ) <=>
% 2.43/2.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.43/2.61  thf('78', plain,
% 2.43/2.61      (![X4 : $i, X6 : $i]:
% 2.43/2.61         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.43/2.61      inference('cnf', [status(esa)], [d3_tarski])).
% 2.43/2.61  thf('79', plain,
% 2.43/2.61      (![X4 : $i, X6 : $i]:
% 2.43/2.61         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 2.43/2.61      inference('cnf', [status(esa)], [d3_tarski])).
% 2.43/2.61  thf('80', plain,
% 2.43/2.61      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['78', '79'])).
% 2.43/2.61  thf('81', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 2.43/2.61      inference('simplify', [status(thm)], ['80'])).
% 2.43/2.61  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.43/2.61  thf('82', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 2.43/2.61      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.43/2.61  thf(t69_xboole_1, axiom,
% 2.43/2.61    (![A:$i,B:$i]:
% 2.43/2.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.43/2.61       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 2.43/2.61  thf('83', plain,
% 2.43/2.61      (![X8 : $i, X9 : $i]:
% 2.43/2.61         (~ (r1_xboole_0 @ X8 @ X9)
% 2.43/2.61          | ~ (r1_tarski @ X8 @ X9)
% 2.43/2.61          | (v1_xboole_0 @ X8))),
% 2.43/2.61      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.43/2.61  thf('84', plain,
% 2.43/2.61      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['82', '83'])).
% 2.43/2.61  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.43/2.61      inference('sup-', [status(thm)], ['81', '84'])).
% 2.43/2.61  thf('86', plain, ((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C_1))),
% 2.43/2.61      inference('demod', [status(thm)], ['11', '77', '85'])).
% 2.43/2.61  thf('87', plain, ((v1_xboole_0 @ sk_E)),
% 2.43/2.61      inference('demod', [status(thm)], ['2', '86'])).
% 2.43/2.61  thf('88', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 2.43/2.61      inference('clc', [status(thm)], ['73', '76'])).
% 2.43/2.61  thf('89', plain,
% 2.43/2.61      (![X13 : $i, X14 : $i]:
% 2.43/2.61         (~ (v1_xboole_0 @ X14)
% 2.43/2.61          | (m1_subset_1 @ X14 @ X13)
% 2.43/2.61          | ~ (v1_xboole_0 @ X13))),
% 2.43/2.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.43/2.61  thf('90', plain,
% 2.43/2.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.43/2.61         (((X32) = (k1_xboole_0))
% 2.43/2.61          | ((X33) = (k4_tarski @ (k1_mcart_1 @ X33) @ (k2_mcart_1 @ X33)))
% 2.43/2.61          | ~ (m1_subset_1 @ X33 @ (k2_zfmisc_1 @ X32 @ X34))
% 2.43/2.61          | ((X34) = (k1_xboole_0)))),
% 2.43/2.61      inference('cnf', [status(esa)], [t24_mcart_1])).
% 2.43/2.61  thf('91', plain,
% 2.43/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.61         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 2.43/2.61          | ~ (v1_xboole_0 @ X2)
% 2.43/2.61          | ((X0) = (k1_xboole_0))
% 2.43/2.61          | ((X2) = (k4_tarski @ (k1_mcart_1 @ X2) @ (k2_mcart_1 @ X2)))
% 2.43/2.61          | ((X1) = (k1_xboole_0)))),
% 2.43/2.61      inference('sup-', [status(thm)], ['89', '90'])).
% 2.43/2.61  thf('92', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (~ (v1_xboole_0 @ k1_xboole_0)
% 2.43/2.61          | ((sk_A) = (k1_xboole_0))
% 2.43/2.61          | ((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0)))
% 2.43/2.61          | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61          | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['88', '91'])).
% 2.43/2.61  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.43/2.61      inference('sup-', [status(thm)], ['81', '84'])).
% 2.43/2.61  thf('94', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((sk_A) = (k1_xboole_0))
% 2.43/2.61          | ((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0)))
% 2.43/2.61          | ((sk_B_2) = (k1_xboole_0))
% 2.43/2.61          | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('demod', [status(thm)], ['92', '93'])).
% 2.43/2.61  thf('95', plain, (((sk_B_2) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('96', plain, (((sk_A) != (k1_xboole_0))),
% 2.43/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.61  thf('97', plain,
% 2.43/2.61      (![X0 : $i]:
% 2.43/2.61         (((X0) = (k4_tarski @ (k1_mcart_1 @ X0) @ (k2_mcart_1 @ X0)))
% 2.43/2.61          | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('simplify_reflect-', [status(thm)], ['94', '95', '96'])).
% 2.43/2.61  thf('98', plain,
% 2.43/2.61      (![X10 : $i, X11 : $i]: ~ (v1_xboole_0 @ (k4_tarski @ X10 @ X11))),
% 2.43/2.61      inference('cnf', [status(esa)], [fc1_zfmisc_1])).
% 2.43/2.61  thf('99', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.43/2.61      inference('sup-', [status(thm)], ['97', '98'])).
% 2.43/2.61  thf('100', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 2.43/2.61      inference('simplify', [status(thm)], ['99'])).
% 2.43/2.61  thf('101', plain, ($false), inference('sup-', [status(thm)], ['87', '100'])).
% 2.43/2.61  
% 2.43/2.61  % SZS output end Refutation
% 2.43/2.61  
% 2.43/2.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
