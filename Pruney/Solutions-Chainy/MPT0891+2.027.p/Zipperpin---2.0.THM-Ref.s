%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a9kJcRa1xh

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:37 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 446 expanded)
%              Number of leaves         :   29 ( 133 expanded)
%              Depth                    :   29
%              Number of atoms          : 1296 (6794 expanded)
%              Number of equality atoms :  169 ( 979 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X19 )
        = ( k2_tarski @ X16 @ X18 ) )
      | ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t51_mcart_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
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
                   != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_mcart_1])).

thf('3',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( X31 = k1_xboole_0 )
      | ( X33
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X30 @ X31 @ X32 @ X33 ) @ ( k6_mcart_1 @ X30 @ X31 @ X32 @ X33 ) @ ( k7_mcart_1 @ X30 @ X31 @ X32 @ X33 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k3_zfmisc_1 @ X30 @ X31 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('5',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_2 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X19 )
        = ( k2_tarski @ X16 @ X18 ) )
      | ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('14',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X15 ) )
        = X14 )
      | ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X17 )
       != ( k2_tarski @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != ( k2_tarski @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('21',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( X1
        = ( sk_B @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X27 @ X26 )
      | ( ( sk_B @ X26 )
       != ( k3_mcart_1 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_1 ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_1 )
         != ( k2_tarski @ X0 @ sk_D_1 ) )
        | ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
        | ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(condensation,[status(thm)],['40'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('43',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_D_1
 != ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X16 @ X18 ) @ X19 )
        = ( k2_tarski @ X16 @ X18 ) )
      | ( r2_hidden @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('48',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('50',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('51',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8'])).

thf('52',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ~ ( r2_hidden @ X28 @ X26 )
      | ( ( sk_B @ X26 )
       != ( k3_mcart_1 @ X28 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_1 )
      | ~ ( r2_hidden @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_1 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,
    ( ( ( ( sk_B @ ( k1_tarski @ sk_D_1 ) )
       != sk_D_1 )
      | ( ( k1_tarski @ sk_D_1 )
        = k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf('58',plain,
    ( ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D_1 @ X0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_1 ) @ k1_xboole_0 )
       != ( k2_tarski @ X0 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','60'])).

thf('62',plain,
    ( ! [X0: $i] :
        ( ( ( k2_tarski @ X0 @ sk_D_1 )
         != ( k2_tarski @ X0 @ sk_D_1 ) )
        | ( r2_hidden @ X0 @ k1_xboole_0 )
        | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
        | ( r2_hidden @ X0 @ k1_xboole_0 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(condensation,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('66',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf('68',plain,
    ( sk_D_1
    = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['46','66','67'])).

thf('69',plain,
    ( sk_D_1
    = ( k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) ),
    inference(simpl_trail,[status(thm)],['11','68'])).

thf('70',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','69'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('71',plain,(
    ! [X34: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X34 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X2 ) )
      | ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_tarski @ ( sk_B_1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( X1
        = ( sk_B_1 @ ( k1_tarski @ X1 ) ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_B_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(condensation,[status(thm)],['75'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('77',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_mcart_1 @ X20 @ X21 @ X22 )
      = ( k4_tarski @ ( k4_tarski @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('78',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( X34 = k1_xboole_0 )
      | ~ ( r2_hidden @ X35 @ X34 )
      | ( ( sk_B_1 @ X34 )
       != ( k4_tarski @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B_1 @ X3 )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) )
      | ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ sk_D_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','69'])).

thf('84',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('86',plain,
    ( ( k1_tarski @ sk_D_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
       != X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_D_1 ) @ k1_xboole_0 )
     != ( k2_tarski @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['2','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k2_tarski @ X0 @ sk_D_1 )
       != ( k2_tarski @ X0 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    r2_hidden @ sk_D_1 @ k1_xboole_0 ),
    inference(condensation,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('94',plain,(
    $false ),
    inference('sup-',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a9kJcRa1xh
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:06:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 174 iterations in 0.104s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.38/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.38/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.56  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.38/0.56  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(t72_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.56       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         (((k4_xboole_0 @ (k2_tarski @ X16 @ X18) @ X19)
% 0.38/0.56            = (k2_tarski @ X16 @ X18))
% 0.38/0.56          | (r2_hidden @ X18 @ X19)
% 0.38/0.56          | (r2_hidden @ X16 @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.38/0.56  thf(d2_tarski, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (((X1) != (X0))
% 0.38/0.56          | (r2_hidden @ X1 @ X2)
% 0.38/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.56  thf(t51_mcart_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ~( ![D:$i]:
% 0.38/0.56               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.38/0.56                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.56                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.56                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.56        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56             ( ~( ![D:$i]:
% 0.38/0.56                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.38/0.56                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.56                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.38/0.56                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_2 @ sk_C))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t48_mcart_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ~( ![D:$i]:
% 0.38/0.56               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.38/0.56                 ( ( D ) =
% 0.38/0.56                   ( k3_mcart_1 @
% 0.38/0.56                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.38/0.56                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.38/0.56                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.56         (((X30) = (k1_xboole_0))
% 0.38/0.56          | ((X31) = (k1_xboole_0))
% 0.38/0.56          | ((X33)
% 0.38/0.56              = (k3_mcart_1 @ (k5_mcart_1 @ X30 @ X31 @ X32 @ X33) @ 
% 0.38/0.56                 (k6_mcart_1 @ X30 @ X31 @ X32 @ X33) @ 
% 0.38/0.56                 (k7_mcart_1 @ X30 @ X31 @ X32 @ X33)))
% 0.38/0.56          | ~ (m1_subset_1 @ X33 @ (k3_zfmisc_1 @ X30 @ X31 @ X32))
% 0.38/0.56          | ((X32) = (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      ((((sk_C) = (k1_xboole_0))
% 0.38/0.56        | ((sk_D_1)
% 0.38/0.56            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56               (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56               (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))
% 0.38/0.56        | ((sk_B_2) = (k1_xboole_0))
% 0.38/0.56        | ((sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.56  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('7', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      (((sk_D_1)
% 0.38/0.56         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))
% 0.38/0.56        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))
% 0.38/0.56        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))
% 0.38/0.56         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('split', [status(esa)], ['10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         (((k4_xboole_0 @ (k2_tarski @ X16 @ X18) @ X19)
% 0.38/0.56            = (k2_tarski @ X16 @ X18))
% 0.38/0.56          | (r2_hidden @ X18 @ X19)
% 0.38/0.56          | (r2_hidden @ X16 @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.56  thf(t29_mcart_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.56                 ( ![C:$i,D:$i,E:$i]:
% 0.38/0.56                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.38/0.56                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('14', plain,
% 0.38/0.56      (![X26 : $i]:
% 0.38/0.56         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.38/0.56  thf(t65_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.38/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      (![X14 : $i, X15 : $i]:
% 0.38/0.56         (((k4_xboole_0 @ X14 @ (k1_tarski @ X15)) = (X14))
% 0.38/0.56          | (r2_hidden @ X15 @ X14))),
% 0.38/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X16 @ X17)
% 0.38/0.56          | ((k4_xboole_0 @ (k2_tarski @ X16 @ X18) @ X17)
% 0.38/0.56              != (k2_tarski @ X16 @ X18)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((k2_tarski @ X1 @ X0) != (k2_tarski @ X1 @ X0))
% 0.38/0.56          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.56          | ~ (r2_hidden @ X1 @ (k1_tarski @ X2)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X2))
% 0.38/0.56          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | (r2_hidden @ X0 @ (k2_tarski @ (sk_B @ (k1_tarski @ X0)) @ X1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['14', '18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.38/0.56          | ((X4) = (X3))
% 0.38/0.56          | ((X4) = (X0))
% 0.38/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (((X4) = (X0))
% 0.38/0.56          | ((X4) = (X3))
% 0.38/0.56          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.38/0.56          | ((X1) = (sk_B @ (k1_tarski @ X1)))
% 0.38/0.56          | ((X1) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['19', '21'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('condensation', [status(thm)], ['22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      (![X26 : $i]:
% 0.38/0.56         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.38/0.56          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('split', [status(esa)], ['10'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (((sk_D_1)
% 0.38/0.56         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.56         (((X26) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X27 @ X26)
% 0.38/0.56          | ((sk_B @ X26) != (k3_mcart_1 @ X28 @ X27 @ X29)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((sk_B @ X0) != (sk_D_1))
% 0.38/0.56          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ X0)
% 0.38/0.56          | ((X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.38/0.56           | ((X0) = (k1_xboole_0))
% 0.38/0.56           | ((sk_B @ X0) != (sk_D_1))))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['27', '30'])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.38/0.56         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.38/0.56         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['26', '31'])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.38/0.56         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('condensation', [status(thm)], ['22'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('clc', [status(thm)], ['33', '34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.38/0.56          | ((k4_xboole_0 @ X14 @ (k1_tarski @ X13)) != (X14)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.38/0.56           | ~ (r2_hidden @ sk_D_1 @ X0)))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_1) @ k1_xboole_0)
% 0.38/0.56            != (k2_tarski @ X0 @ sk_D_1)))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['13', '37'])).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (((k2_tarski @ X0 @ sk_D_1) != (k2_tarski @ X0 @ sk_D_1))
% 0.38/0.56           | (r2_hidden @ X0 @ k1_xboole_0)
% 0.38/0.56           | (r2_hidden @ sk_D_1 @ k1_xboole_0)))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '38'])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((r2_hidden @ sk_D_1 @ k1_xboole_0) | (r2_hidden @ X0 @ k1_xboole_0)))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['39'])).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (((r2_hidden @ sk_D_1 @ k1_xboole_0))
% 0.38/0.56         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('condensation', [status(thm)], ['40'])).
% 0.38/0.56  thf(t113_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf('42', plain,
% 0.38/0.56      (![X9 : $i, X10 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['42'])).
% 0.38/0.56  thf(t152_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.38/0.56      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.38/0.56  thf('45', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (~ (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['41', '45'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.38/0.56         (((k4_xboole_0 @ (k2_tarski @ X16 @ X18) @ X19)
% 0.38/0.56            = (k2_tarski @ X16 @ X18))
% 0.38/0.56          | (r2_hidden @ X18 @ X19)
% 0.38/0.56          | (r2_hidden @ X16 @ X19))),
% 0.38/0.56      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['1'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('split', [status(esa)], ['10'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      (((sk_D_1)
% 0.38/0.56         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8'])).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.56         (((X26) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X28 @ X26)
% 0.38/0.56          | ((sk_B @ X26) != (k3_mcart_1 @ X28 @ X27 @ X29)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((sk_B @ X0) != (sk_D_1))
% 0.38/0.56          | ~ (r2_hidden @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ X0)
% 0.38/0.56          | ((X0) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (~ (r2_hidden @ sk_D_1 @ X0)
% 0.38/0.56           | ((X0) = (k1_xboole_0))
% 0.38/0.56           | ((sk_B @ X0) != (sk_D_1))))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['50', '53'])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (((((k1_tarski @ sk_D_1) = (k1_xboole_0))
% 0.38/0.56         | ((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.38/0.56         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['49', '54'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (((((sk_B @ (k1_tarski @ sk_D_1)) != (sk_D_1))
% 0.38/0.56         | ((k1_tarski @ sk_D_1) = (k1_xboole_0))))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ((X0) = (sk_B @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('condensation', [status(thm)], ['22'])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      ((((k1_tarski @ sk_D_1) = (k1_xboole_0)))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('clc', [status(thm)], ['56', '57'])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.38/0.56          | ((k4_xboole_0 @ X14 @ (k1_tarski @ X13)) != (X14)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.38/0.56           | ~ (r2_hidden @ sk_D_1 @ X0)))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_1) @ k1_xboole_0)
% 0.38/0.56            != (k2_tarski @ X0 @ sk_D_1)))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['48', '60'])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          (((k2_tarski @ X0 @ sk_D_1) != (k2_tarski @ X0 @ sk_D_1))
% 0.38/0.56           | (r2_hidden @ X0 @ k1_xboole_0)
% 0.38/0.56           | (r2_hidden @ sk_D_1 @ k1_xboole_0)))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['47', '61'])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      ((![X0 : $i]:
% 0.38/0.56          ((r2_hidden @ sk_D_1 @ k1_xboole_0) | (r2_hidden @ X0 @ k1_xboole_0)))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['62'])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      (((r2_hidden @ sk_D_1 @ k1_xboole_0))
% 0.38/0.56         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))))),
% 0.38/0.56      inference('condensation', [status(thm)], ['63'])).
% 0.38/0.56  thf('65', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      (~ (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))) | 
% 0.38/0.56       (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))) | 
% 0.38/0.56       (((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('split', [status(esa)], ['10'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)], ['46', '66', '67'])).
% 0.38/0.56  thf('69', plain, (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['11', '68'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (((sk_D_1)
% 0.38/0.56         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ sk_D_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '69'])).
% 0.38/0.56  thf(t9_mcart_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ![B:$i]:
% 0.38/0.56            ( ~( ( r2_hidden @ B @ A ) & 
% 0.38/0.56                 ( ![C:$i,D:$i]:
% 0.38/0.56                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.38/0.56                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      (![X34 : $i]:
% 0.38/0.56         (((X34) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X34) @ X34))),
% 0.38/0.56      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ X2))
% 0.38/0.56          | (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | (r2_hidden @ X0 @ (k2_tarski @ (sk_B_1 @ (k1_tarski @ X0)) @ X1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['71', '72'])).
% 0.38/0.56  thf('74', plain,
% 0.38/0.56      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.38/0.56         (((X4) = (X0))
% 0.38/0.56          | ((X4) = (X3))
% 0.38/0.56          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['20'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k1_tarski @ X1) = (k1_xboole_0))
% 0.38/0.56          | ((X1) = (sk_B_1 @ (k1_tarski @ X1)))
% 0.38/0.56          | ((X1) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ((X0) = (sk_B_1 @ (k1_tarski @ X0))))),
% 0.38/0.56      inference('condensation', [status(thm)], ['75'])).
% 0.38/0.56  thf(d3_mcart_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.38/0.56         ((k3_mcart_1 @ X20 @ X21 @ X22)
% 0.38/0.56           = (k4_tarski @ (k4_tarski @ X20 @ X21) @ X22))),
% 0.38/0.56      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.38/0.56  thf('78', plain,
% 0.38/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.38/0.56         (((X34) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X35 @ X34)
% 0.38/0.56          | ((sk_B_1 @ X34) != (k4_tarski @ X36 @ X35)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (((sk_B_1 @ X3) != (k3_mcart_1 @ X2 @ X1 @ X0))
% 0.38/0.56          | ~ (r2_hidden @ X0 @ X3)
% 0.38/0.56          | ((X3) = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['77', '78'])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.38/0.56          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['76', '79'])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X1 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))
% 0.38/0.56          | ((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['80'])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))
% 0.38/0.56        | ((k1_tarski @ 
% 0.38/0.56            (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56             (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ sk_D_1))
% 0.38/0.56            = (k1_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['70', '81'])).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      (((sk_D_1)
% 0.38/0.56         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ 
% 0.38/0.56            (k6_mcart_1 @ sk_A @ sk_B_2 @ sk_C @ sk_D_1) @ sk_D_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '69'])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))
% 0.38/0.56        | ((k1_tarski @ sk_D_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['82', '83'])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.38/0.56          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['25'])).
% 0.38/0.56  thf('86', plain, (((k1_tarski @ sk_D_1) = (k1_xboole_0))),
% 0.38/0.56      inference('clc', [status(thm)], ['84', '85'])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X13 @ X14)
% 0.38/0.56          | ((k4_xboole_0 @ X14 @ (k1_tarski @ X13)) != (X14)))),
% 0.38/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.38/0.56          | ~ (r2_hidden @ sk_D_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['86', '87'])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_D_1) @ k1_xboole_0)
% 0.38/0.56           != (k2_tarski @ X0 @ sk_D_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['2', '88'])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (((k2_tarski @ X0 @ sk_D_1) != (k2_tarski @ X0 @ sk_D_1))
% 0.38/0.56          | (r2_hidden @ X0 @ k1_xboole_0)
% 0.38/0.56          | (r2_hidden @ sk_D_1 @ k1_xboole_0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['0', '89'])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((r2_hidden @ sk_D_1 @ k1_xboole_0) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['90'])).
% 0.38/0.56  thf('92', plain, ((r2_hidden @ sk_D_1 @ k1_xboole_0)),
% 0.38/0.56      inference('condensation', [status(thm)], ['91'])).
% 0.38/0.56  thf('93', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '44'])).
% 0.38/0.56  thf('94', plain, ($false), inference('sup-', [status(thm)], ['92', '93'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
