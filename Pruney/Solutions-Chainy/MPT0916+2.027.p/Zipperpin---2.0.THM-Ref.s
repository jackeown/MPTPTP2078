%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Y5xeV0D5M

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 529 expanded)
%              Number of leaves         :   29 ( 174 expanded)
%              Depth                    :   26
%              Number of atoms          : 1338 (7939 expanded)
%              Number of equality atoms :   84 ( 135 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('6',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
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

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('16',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_G ) @ ( k2_zfmisc_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('22',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('29',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k2_mcart_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('31',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k2_mcart_1 @ sk_G ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('33',plain,
    ( ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_G @ ( k3_zfmisc_1 @ sk_D @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k3_zfmisc_1 @ X12 @ X13 @ X14 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k2_mcart_1 @ X3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('40',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('43',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
        | ~ ( r1_tarski @ X1 @ X0 )
        | ( r1_xboole_0 @ sk_F @ X1 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('44',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A = k1_xboole_0 )
        | ( sk_B = k1_xboole_0 )
        | ~ ( r1_tarski @ X1 @ X0 )
        | ( r1_xboole_0 @ sk_F @ X1 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(demod,[status(thm)],['43','51'])).

thf('53',plain,
    ( ( ( r1_xboole_0 @ sk_F @ sk_F )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['28','52'])).

thf('54',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['34','37'])).

thf('55',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['34','37'])).

thf('56',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_G ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(clc,[status(thm)],['53','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('65',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ sk_E @ X1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_E @ sk_E ) )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('71',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_E ),
    inference('sup-',[status(thm)],['20','21'])).

thf('72',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(clc,[status(thm)],['69','74'])).

thf('76',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('77',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('79',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('80',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ sk_D @ X1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_D )
   <= ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('85',plain,(
    r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_G @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X18 @ X19 @ X21 @ X20 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k3_zfmisc_1 @ X18 @ X19 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('88',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(split,[status(esa)],['17'])).

thf('90',plain,
    ( ( ~ ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_G ) ) @ sk_D ),
    inference('sup-',[status(thm)],['4','5'])).

thf('92',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C_1 = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('94',plain,
    ( ( ( r1_tarski @ sk_F @ k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('96',plain,(
    r1_tarski @ sk_F @ sk_C_1 ),
    inference('sup-',[status(thm)],['24','25'])).

thf('97',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ~ ( r1_tarski @ X5 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ sk_F @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_F @ sk_F ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('102',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('104',plain,
    ( ( ( r1_tarski @ sk_E @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('106',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_E @ sk_E ) )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('108',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    r1_tarski @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('110',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('112',plain,
    ( ( r1_xboole_0 @ sk_D @ sk_D )
   <= ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( r1_xboole_0 @ sk_D @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('114',plain,(
    r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E )
    | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_D )
    | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('116',plain,(
    ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G ) @ sk_E ) ),
    inference('sat_resolution*',[status(thm)],['85','114','115'])).

thf('117',plain,
    ( ( r1_tarski @ sk_F @ k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['27','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_F @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('119',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( r1_xboole_0 @ sk_F @ sk_F ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('121',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    r1_tarski @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['60','61'])).

thf('123',plain,
    ( ( r1_tarski @ sk_E @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_E @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('125',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( r1_xboole_0 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('127',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    r1_tarski @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('130',plain,(
    r1_xboole_0 @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    $false ),
    inference(demod,[status(thm)],['10','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4Y5xeV0D5M
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 323 iterations in 0.145s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.60  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.60  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.60  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.60  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.60  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.60  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(t76_mcart_1, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.60       ( ![E:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.60           ( ![F:$i]:
% 0.21/0.60             ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.60               ( ![G:$i]:
% 0.21/0.60                 ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.60                   ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.60                     ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.60                       ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.60                       ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.60          ( ![E:$i]:
% 0.21/0.60            ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) =>
% 0.21/0.60              ( ![F:$i]:
% 0.21/0.60                ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ C ) ) =>
% 0.21/0.60                  ( ![G:$i]:
% 0.21/0.60                    ( ( m1_subset_1 @ G @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.60                      ( ( r2_hidden @ G @ ( k3_zfmisc_1 @ D @ E @ F ) ) =>
% 0.21/0.60                        ( ( r2_hidden @ ( k5_mcart_1 @ A @ B @ C @ G ) @ D ) & 
% 0.21/0.60                          ( r2_hidden @ ( k6_mcart_1 @ A @ B @ C @ G ) @ E ) & 
% 0.21/0.60                          ( r2_hidden @ ( k7_mcart_1 @ A @ B @ C @ G ) @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t76_mcart_1])).
% 0.21/0.60  thf('0', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(d3_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.21/0.60       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.60         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.21/0.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.60  thf(t10_mcart_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.60       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.60         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.60         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.21/0.60          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.60          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.60         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.21/0.60          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.60  thf('6', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.60  thf('7', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.60  thf(t3_xboole_0, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.60            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.60  thf('8', plain,
% 0.21/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.21/0.60          | ~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.60  thf('10', plain, (~ (r1_xboole_0 @ sk_D @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.60  thf('11', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t3_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (![X9 : $i, X10 : $i]:
% 0.21/0.60         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('13', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t50_mcart_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ~( ![D:$i]:
% 0.21/0.60               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.60                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.60                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.60                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.21/0.60                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.21/0.60                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.60         (((X18) = (k1_xboole_0))
% 0.21/0.60          | ((X19) = (k1_xboole_0))
% 0.21/0.60          | ((k6_mcart_1 @ X18 @ X19 @ X21 @ X20)
% 0.21/0.60              = (k2_mcart_1 @ (k1_mcart_1 @ X20)))
% 0.21/0.60          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.21/0.60          | ((X21) = (k1_xboole_0)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.21/0.60            = (k2_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.60        | ((sk_B) = (k1_xboole_0))
% 0.21/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)
% 0.21/0.60        | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)
% 0.21/0.60        | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      ((~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.21/0.60      inference('split', [status(esa)], ['17'])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (((~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['16', '18'])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      ((r2_hidden @ (k1_mcart_1 @ sk_G) @ (k2_zfmisc_1 @ sk_D @ sk_E))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '3'])).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.60         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.21/0.60          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.60  thf('22', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.21/0.60      inference('demod', [status(thm)], ['19', '22'])).
% 0.21/0.60  thf('24', plain, ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (![X9 : $i, X10 : $i]:
% 0.21/0.60         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('26', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['23', '26'])).
% 0.21/0.60  thf('28', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.60         (((X18) = (k1_xboole_0))
% 0.21/0.60          | ((X19) = (k1_xboole_0))
% 0.21/0.60          | ((k7_mcart_1 @ X18 @ X19 @ X21 @ X20) = (k2_mcart_1 @ X20))
% 0.21/0.60          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.21/0.60          | ((X21) = (k1_xboole_0)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) = (k2_mcart_1 @ sk_G))
% 0.21/0.60        | ((sk_B) = (k1_xboole_0))
% 0.21/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.60  thf('32', plain,
% 0.21/0.60      ((~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('split', [status(esa)], ['17'])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      (((~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.60  thf('34', plain, ((r2_hidden @ sk_G @ (k3_zfmisc_1 @ sk_D @ sk_E @ sk_F))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('35', plain,
% 0.21/0.60      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.60         ((k3_zfmisc_1 @ X12 @ X13 @ X14)
% 0.21/0.60           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13) @ X14))),
% 0.21/0.60      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.60         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.21/0.60          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.21/0.60          | (r2_hidden @ (k2_mcart_1 @ X3) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.60  thf('38', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('demod', [status(thm)], ['33', '38'])).
% 0.21/0.60  thf('40', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf(t64_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.21/0.60         ( r1_xboole_0 @ B @ D ) ) =>
% 0.21/0.60       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X4 @ X5)
% 0.21/0.60          | ~ (r1_tarski @ X4 @ X6)
% 0.21/0.60          | ~ (r1_tarski @ X5 @ X7)
% 0.21/0.60          | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      ((![X0 : $i, X1 : $i]:
% 0.21/0.60          (((sk_A) = (k1_xboole_0))
% 0.21/0.60           | ((sk_B) = (k1_xboole_0))
% 0.21/0.60           | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.60           | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.60           | (r1_xboole_0 @ sk_F @ X1)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.60  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.60  thf('44', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.60  thf('46', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.60          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.21/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.60  thf('49', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.21/0.60          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['45', '48'])).
% 0.21/0.60  thf('50', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.60      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.60  thf('51', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['44', '50'])).
% 0.21/0.60  thf('52', plain,
% 0.21/0.60      ((![X0 : $i, X1 : $i]:
% 0.21/0.60          (((sk_A) = (k1_xboole_0))
% 0.21/0.60           | ((sk_B) = (k1_xboole_0))
% 0.21/0.60           | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.60           | (r1_xboole_0 @ sk_F @ X1)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('demod', [status(thm)], ['43', '51'])).
% 0.21/0.60  thf('53', plain,
% 0.21/0.60      ((((r1_xboole_0 @ sk_F @ sk_F)
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '52'])).
% 0.21/0.60  thf('54', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.60  thf('55', plain, ((r2_hidden @ (k2_mcart_1 @ sk_G) @ sk_F)),
% 0.21/0.60      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.60  thf('56', plain,
% 0.21/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.60  thf('57', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ sk_F @ X0)
% 0.21/0.60          | ~ (r2_hidden @ (k2_mcart_1 @ sk_G) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.60  thf('58', plain, (~ (r1_xboole_0 @ sk_F @ sk_F)),
% 0.21/0.60      inference('sup-', [status(thm)], ['54', '57'])).
% 0.21/0.60  thf('59', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('clc', [status(thm)], ['53', '58'])).
% 0.21/0.60  thf('60', plain, ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('61', plain,
% 0.21/0.60      (![X9 : $i, X10 : $i]:
% 0.21/0.60         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('62', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.60  thf('63', plain,
% 0.21/0.60      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['59', '62'])).
% 0.21/0.60  thf('64', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.60  thf('65', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.60  thf('66', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X4 @ X5)
% 0.21/0.60          | ~ (r1_tarski @ X4 @ X6)
% 0.21/0.60          | ~ (r1_tarski @ X5 @ X7)
% 0.21/0.60          | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.60  thf('67', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.60          | (r1_xboole_0 @ sk_E @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.60  thf('68', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_E @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['64', '67'])).
% 0.21/0.60  thf('69', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_E @ sk_E)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['63', '68'])).
% 0.21/0.60  thf('70', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.60  thf('71', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_E)),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.60  thf('72', plain,
% 0.21/0.60      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.60         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.60          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.60          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.60  thf('73', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ sk_E @ X0)
% 0.21/0.60          | ~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_G)) @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.60  thf('74', plain, (~ (r1_xboole_0 @ sk_E @ sk_E)),
% 0.21/0.60      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.60  thf('75', plain,
% 0.21/0.60      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('clc', [status(thm)], ['69', '74'])).
% 0.21/0.60  thf('76', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('77', plain,
% 0.21/0.60      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['75', '76'])).
% 0.21/0.60  thf('78', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.60  thf('79', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('80', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X4 @ X5)
% 0.21/0.60          | ~ (r1_tarski @ X4 @ X6)
% 0.21/0.60          | ~ (r1_tarski @ X5 @ X7)
% 0.21/0.60          | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.60  thf('81', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ sk_A @ X0)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.60          | (r1_xboole_0 @ sk_D @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.60  thf('82', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_D @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['78', '81'])).
% 0.21/0.60  thf('83', plain,
% 0.21/0.60      (((r1_xboole_0 @ sk_D @ sk_D))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['77', '82'])).
% 0.21/0.60  thf('84', plain, (~ (r1_xboole_0 @ sk_D @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.60  thf('85', plain,
% 0.21/0.60      (((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.60      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.60  thf('86', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_G @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C_1))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('87', plain,
% 0.21/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.60         (((X18) = (k1_xboole_0))
% 0.21/0.60          | ((X19) = (k1_xboole_0))
% 0.21/0.60          | ((k5_mcart_1 @ X18 @ X19 @ X21 @ X20)
% 0.21/0.60              = (k1_mcart_1 @ (k1_mcart_1 @ X20)))
% 0.21/0.60          | ~ (m1_subset_1 @ X20 @ (k3_zfmisc_1 @ X18 @ X19 @ X21))
% 0.21/0.60          | ((X21) = (k1_xboole_0)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.21/0.60  thf('88', plain,
% 0.21/0.60      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.60        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G)
% 0.21/0.60            = (k1_mcart_1 @ (k1_mcart_1 @ sk_G)))
% 0.21/0.60        | ((sk_B) = (k1_xboole_0))
% 0.21/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.60  thf('89', plain,
% 0.21/0.60      ((~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('split', [status(esa)], ['17'])).
% 0.21/0.60  thf('90', plain,
% 0.21/0.60      (((~ (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.60  thf('91', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_G)) @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.60  thf('92', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_C_1) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.60  thf('93', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('94', plain,
% 0.21/0.60      ((((r1_tarski @ sk_F @ k1_xboole_0)
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['92', '93'])).
% 0.21/0.60  thf('95', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.60      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.60  thf('96', plain, ((r1_tarski @ sk_F @ sk_C_1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.60  thf('97', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ X4 @ X5)
% 0.21/0.60          | ~ (r1_tarski @ X4 @ X6)
% 0.21/0.60          | ~ (r1_tarski @ X5 @ X7)
% 0.21/0.60          | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.60  thf('98', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.60          | (r1_xboole_0 @ sk_F @ X1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.60  thf('99', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_F @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['95', '98'])).
% 0.21/0.60  thf('100', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0))
% 0.21/0.60         | ((sk_B) = (k1_xboole_0))
% 0.21/0.60         | (r1_xboole_0 @ sk_F @ sk_F)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['94', '99'])).
% 0.21/0.60  thf('101', plain, (~ (r1_xboole_0 @ sk_F @ sk_F)),
% 0.21/0.60      inference('sup-', [status(thm)], ['54', '57'])).
% 0.21/0.60  thf('102', plain,
% 0.21/0.60      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('clc', [status(thm)], ['100', '101'])).
% 0.21/0.60  thf('103', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.60  thf('104', plain,
% 0.21/0.60      ((((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['102', '103'])).
% 0.21/0.60  thf('105', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_E @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['64', '67'])).
% 0.21/0.60  thf('106', plain,
% 0.21/0.60      (((((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_E @ sk_E)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['104', '105'])).
% 0.21/0.60  thf('107', plain, (~ (r1_xboole_0 @ sk_E @ sk_E)),
% 0.21/0.60      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.60  thf('108', plain,
% 0.21/0.60      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('clc', [status(thm)], ['106', '107'])).
% 0.21/0.60  thf('109', plain, ((r1_tarski @ sk_D @ sk_A)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('110', plain,
% 0.21/0.60      (((r1_tarski @ sk_D @ k1_xboole_0))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['108', '109'])).
% 0.21/0.60  thf('111', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_D @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['78', '81'])).
% 0.21/0.60  thf('112', plain,
% 0.21/0.60      (((r1_xboole_0 @ sk_D @ sk_D))
% 0.21/0.60         <= (~
% 0.21/0.60             ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['110', '111'])).
% 0.21/0.60  thf('113', plain, (~ (r1_xboole_0 @ sk_D @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.60  thf('114', plain,
% 0.21/0.60      (((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D))),
% 0.21/0.60      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.60  thf('115', plain,
% 0.21/0.60      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E)) | 
% 0.21/0.60       ~ ((r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_D)) | 
% 0.21/0.60       ~ ((r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_F))),
% 0.21/0.60      inference('split', [status(esa)], ['17'])).
% 0.21/0.60  thf('116', plain,
% 0.21/0.60      (~ ((r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B @ sk_C_1 @ sk_G) @ sk_E))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['85', '114', '115'])).
% 0.21/0.60  thf('117', plain,
% 0.21/0.60      (((r1_tarski @ sk_F @ k1_xboole_0)
% 0.21/0.60        | ((sk_B) = (k1_xboole_0))
% 0.21/0.60        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['27', '116'])).
% 0.21/0.60  thf('118', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_F @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['95', '98'])).
% 0.21/0.60  thf('119', plain,
% 0.21/0.60      ((((sk_A) = (k1_xboole_0))
% 0.21/0.60        | ((sk_B) = (k1_xboole_0))
% 0.21/0.60        | (r1_xboole_0 @ sk_F @ sk_F))),
% 0.21/0.60      inference('sup-', [status(thm)], ['117', '118'])).
% 0.21/0.60  thf('120', plain, (~ (r1_xboole_0 @ sk_F @ sk_F)),
% 0.21/0.60      inference('sup-', [status(thm)], ['54', '57'])).
% 0.21/0.60  thf('121', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.60      inference('clc', [status(thm)], ['119', '120'])).
% 0.21/0.60  thf('122', plain, ((r1_tarski @ sk_E @ sk_B)),
% 0.21/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.60  thf('123', plain,
% 0.21/0.60      (((r1_tarski @ sk_E @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup+', [status(thm)], ['121', '122'])).
% 0.21/0.60  thf('124', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_E @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['64', '67'])).
% 0.21/0.60  thf('125', plain, ((((sk_A) = (k1_xboole_0)) | (r1_xboole_0 @ sk_E @ sk_E))),
% 0.21/0.60      inference('sup-', [status(thm)], ['123', '124'])).
% 0.21/0.60  thf('126', plain, (~ (r1_xboole_0 @ sk_E @ sk_E)),
% 0.21/0.60      inference('sup-', [status(thm)], ['70', '73'])).
% 0.21/0.60  thf('127', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.60      inference('clc', [status(thm)], ['125', '126'])).
% 0.21/0.60  thf('128', plain, ((r1_tarski @ sk_D @ k1_xboole_0)),
% 0.21/0.60      inference('demod', [status(thm)], ['13', '127'])).
% 0.21/0.60  thf('129', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_xboole_0 @ sk_D @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['78', '81'])).
% 0.21/0.60  thf('130', plain, ((r1_xboole_0 @ sk_D @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['128', '129'])).
% 0.21/0.60  thf('131', plain, ($false), inference('demod', [status(thm)], ['10', '130'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.21/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
