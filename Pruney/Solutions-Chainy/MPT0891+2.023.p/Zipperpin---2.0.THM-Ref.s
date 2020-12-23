%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CFoy70D6Zj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:36 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 431 expanded)
%              Number of leaves         :   23 ( 131 expanded)
%              Depth                    :   20
%              Number of atoms          : 1279 (6419 expanded)
%              Number of equality atoms :  157 ( 877 expanded)
%              Maximal formula depth    :   20 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X9 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('1',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['0'])).

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

thf('2',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('3',plain,(
    ! [X6: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ( X10 = X9 )
      | ( X10 = X6 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('4',plain,(
    ! [X6: $i,X9: $i,X10: $i] :
      ( ( X10 = X6 )
      | ( X10 = X9 )
      | ~ ( r2_hidden @ X10 @ ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X28 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X14 @ X16 ) @ X15 )
       != ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(clc,[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k4_tarski @ X2 @ X1 ) )
      | ( ( sk_B @ ( k2_tarski @ X3 @ X0 ) )
        = X3 )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X3 @ X0 ) )
      | ( ( k2_tarski @ X3 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) ) )
      | ( ( sk_B @ ( k2_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) ) )
        = X3 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('25',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) ) )
        = X3 )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X3 @ ( k4_tarski @ X2 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B @ ( k2_tarski @ X0 @ ( k4_tarski @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','25'])).

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

thf('27',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_2 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
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

thf('30',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( X27
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X24 @ X25 @ X26 @ X27 ) @ ( k6_mcart_1 @ X24 @ X25 @ X26 @ X27 ) @ ( k7_mcart_1 @ X24 @ X25 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k3_zfmisc_1 @ X24 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('31',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('36',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ sk_D_2 @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X6 )
      | ( r2_hidden @ X7 @ X8 )
      | ( X8
       != ( k2_tarski @ X9 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('38',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X6 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('39',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X30 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B @ X3 )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_tarski @ X2 @ ( k4_tarski @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X2 @ ( k4_tarski @ X1 @ X0 ) ) )
       != ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B @ ( k2_tarski @ X2 @ ( k4_tarski @ X1 @ X0 ) ) )
     != ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ X0 @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ sk_D_2 ) ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(clc,[status(thm)],['5','19'])).

thf('47',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('48',plain,
    ( ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('49',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('50',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r2_hidden @ X29 @ X28 )
      | ( ( sk_B @ X28 )
       != ( k4_tarski @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B @ X3 )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D_2 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_D_2 @ X0 )
        | ( X0 = k1_xboole_0 )
        | ( ( sk_B @ X0 )
         != sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
         != sk_D_2 )
        | ( ( k2_tarski @ sk_D_2 @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_D_2 )
        | ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
          = sk_D_2 ) )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['46','57'])).

thf('59',plain,
    ( ( ( sk_B @ ( k2_tarski @ sk_D_2 @ sk_D_2 ) )
      = sk_D_2 )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( sk_B @ ( k2_tarski @ sk_D_2 @ X0 ) )
       != sk_D_2 )
   <= ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('61',plain,(
    sk_D_2
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('63',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('64',plain,
    ( ( sk_D_2
      = ( k3_mcart_1 @ sk_D_2 @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X1 @ X0 ) )
        = X1 ) ) ),
    inference(clc,[status(thm)],['5','19'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B @ ( k2_tarski @ X2 @ ( k4_tarski @ X1 @ X0 ) ) )
     != ( k3_mcart_1 @ X1 @ X0 @ X3 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ( ( sk_B @ ( k2_tarski @ X0 @ ( k4_tarski @ X3 @ X2 ) ) )
        = ( k4_tarski @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( sk_B @ ( k2_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ ( k4_tarski @ X3 @ X2 ) ) )
      = ( k4_tarski @ X3 @ X2 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_mcart_1 @ ( k4_tarski @ X2 @ X1 ) @ X0 @ X3 )
      = ( k4_tarski @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X6: $i,X9: $i] :
      ( r2_hidden @ X9 @ ( k2_tarski @ X9 @ X6 ) ) ),
    inference(simplify,[status(thm)],['0'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( sk_B @ X3 )
       != ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ X3 )
      | ( X3 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) )
       != ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( sk_B @ ( k2_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 ) )
     != ( k3_mcart_1 @ X2 @ X1 @ X3 ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( sk_B @ ( k2_tarski @ ( k3_mcart_1 @ ( k4_tarski @ X3 @ X2 ) @ X1 @ X0 ) @ X5 ) )
     != ( k3_mcart_1 @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) @ X0 @ X4 ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k4_tarski @ ( k4_tarski @ X2 @ X1 ) @ X0 )
     != ( k3_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X4 @ X3 ) ) ),
    inference('sup-',[status(thm)],['69','78'])).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_mcart_1 @ X18 @ X19 @ X20 )
      = ( k4_tarski @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != ( k3_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) @ X4 @ X3 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
     != ( k3_mcart_1 @ sk_D_2 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','81'])).

thf('83',plain,
    ( sk_D_2
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33','34'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( sk_D_2
     != ( k3_mcart_1 @ sk_D_2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_D_2 != sk_D_2 )
   <= ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['64','84'])).

thf('86',plain,(
    sk_D_2
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_D_2
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) )
    | ( sk_D_2
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ) ),
    inference(split,[status(esa)],['27'])).

thf('88',plain,
    ( sk_D_2
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) ),
    inference('sat_resolution*',[status(thm)],['61','86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k2_tarski @ X0 @ ( k4_tarski @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2 ) @ sk_D_2 ) ) )
     != sk_D_2 ) ),
    inference(simpl_trail,[status(thm)],['45','88'])).

thf('90',plain,(
    sk_D_2 != sk_D_2 ),
    inference('sup-',[status(thm)],['26','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CFoy70D6Zj
% 0.13/0.37  % Computer   : n021.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 19:17:05 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 1.17/1.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.17/1.42  % Solved by: fo/fo7.sh
% 1.17/1.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.17/1.42  % done 1489 iterations in 0.940s
% 1.17/1.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.17/1.42  % SZS output start Refutation
% 1.17/1.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.17/1.42  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 1.17/1.42  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.17/1.42  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.17/1.42  thf(sk_C_type, type, sk_C: $i).
% 1.17/1.42  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.17/1.42  thf(sk_A_type, type, sk_A: $i).
% 1.17/1.42  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.17/1.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.17/1.42  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.17/1.42  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 1.17/1.42  thf(sk_B_type, type, sk_B: $i > $i).
% 1.17/1.42  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 1.17/1.42  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 1.17/1.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.17/1.42  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.17/1.42  thf(d2_tarski, axiom,
% 1.17/1.42    (![A:$i,B:$i,C:$i]:
% 1.17/1.42     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.17/1.42       ( ![D:$i]:
% 1.17/1.42         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.17/1.42  thf('0', plain,
% 1.17/1.42      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.17/1.42         (((X7) != (X9))
% 1.17/1.42          | (r2_hidden @ X7 @ X8)
% 1.17/1.42          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 1.17/1.42      inference('cnf', [status(esa)], [d2_tarski])).
% 1.17/1.42  thf('1', plain,
% 1.17/1.42      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 1.17/1.42      inference('simplify', [status(thm)], ['0'])).
% 1.17/1.42  thf(t9_mcart_1, axiom,
% 1.17/1.42    (![A:$i]:
% 1.17/1.42     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42          ( ![B:$i]:
% 1.17/1.42            ( ~( ( r2_hidden @ B @ A ) & 
% 1.17/1.42                 ( ![C:$i,D:$i]:
% 1.17/1.42                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.17/1.42                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.17/1.42  thf('2', plain,
% 1.17/1.42      (![X28 : $i]:
% 1.17/1.42         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 1.17/1.42      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.17/1.42  thf('3', plain,
% 1.17/1.42      (![X6 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 1.17/1.42         (~ (r2_hidden @ X10 @ X8)
% 1.17/1.42          | ((X10) = (X9))
% 1.17/1.42          | ((X10) = (X6))
% 1.17/1.42          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 1.17/1.42      inference('cnf', [status(esa)], [d2_tarski])).
% 1.17/1.42  thf('4', plain,
% 1.17/1.42      (![X6 : $i, X9 : $i, X10 : $i]:
% 1.17/1.42         (((X10) = (X6))
% 1.17/1.42          | ((X10) = (X9))
% 1.17/1.42          | ~ (r2_hidden @ X10 @ (k2_tarski @ X9 @ X6)))),
% 1.17/1.42      inference('simplify', [status(thm)], ['3'])).
% 1.17/1.42  thf('5', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((k2_tarski @ X1 @ X0) = (k1_xboole_0))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['2', '4'])).
% 1.17/1.42  thf('6', plain,
% 1.17/1.42      (![X28 : $i]:
% 1.17/1.42         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 1.17/1.42      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.17/1.42  thf(d5_xboole_0, axiom,
% 1.17/1.42    (![A:$i,B:$i,C:$i]:
% 1.17/1.42     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 1.17/1.42       ( ![D:$i]:
% 1.17/1.42         ( ( r2_hidden @ D @ C ) <=>
% 1.17/1.42           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 1.17/1.42  thf('7', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.42         (~ (r2_hidden @ X4 @ X3)
% 1.17/1.42          | (r2_hidden @ X4 @ X1)
% 1.17/1.42          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.42      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.17/1.42  thf('8', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.17/1.42         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.42      inference('simplify', [status(thm)], ['7'])).
% 1.17/1.42  thf('9', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.17/1.42          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 1.17/1.42      inference('sup-', [status(thm)], ['6', '8'])).
% 1.17/1.42  thf('10', plain,
% 1.17/1.42      (![X28 : $i]:
% 1.17/1.42         (((X28) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X28) @ X28))),
% 1.17/1.42      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.17/1.42  thf('11', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.42         (~ (r2_hidden @ X4 @ X3)
% 1.17/1.42          | ~ (r2_hidden @ X4 @ X2)
% 1.17/1.42          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.42      inference('cnf', [status(esa)], [d5_xboole_0])).
% 1.17/1.42  thf('12', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.17/1.42         (~ (r2_hidden @ X4 @ X2)
% 1.17/1.42          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 1.17/1.42      inference('simplify', [status(thm)], ['11'])).
% 1.17/1.42  thf('13', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.17/1.42          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 1.17/1.42      inference('sup-', [status(thm)], ['10', '12'])).
% 1.17/1.42  thf('14', plain,
% 1.17/1.42      (![X0 : $i]:
% 1.17/1.42         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 1.17/1.42          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['9', '13'])).
% 1.17/1.42  thf('15', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.17/1.42      inference('simplify', [status(thm)], ['14'])).
% 1.17/1.42  thf(t72_zfmisc_1, axiom,
% 1.17/1.42    (![A:$i,B:$i,C:$i]:
% 1.17/1.42     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.17/1.42       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 1.17/1.42  thf('16', plain,
% 1.17/1.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.17/1.42         (~ (r2_hidden @ X14 @ X15)
% 1.17/1.42          | ((k4_xboole_0 @ (k2_tarski @ X14 @ X16) @ X15)
% 1.17/1.42              != (k2_tarski @ X14 @ X16)))),
% 1.17/1.42      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 1.17/1.42  thf('17', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((k1_xboole_0) != (k2_tarski @ X1 @ X0))
% 1.17/1.42          | ~ (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['15', '16'])).
% 1.17/1.42  thf('18', plain,
% 1.17/1.42      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 1.17/1.42      inference('simplify', [status(thm)], ['0'])).
% 1.17/1.42  thf('19', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 1.17/1.42      inference('demod', [status(thm)], ['17', '18'])).
% 1.17/1.42  thf('20', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X0))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 1.17/1.42      inference('clc', [status(thm)], ['5', '19'])).
% 1.17/1.42  thf('21', plain,
% 1.17/1.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.17/1.42         (((X28) = (k1_xboole_0))
% 1.17/1.42          | ~ (r2_hidden @ X29 @ X28)
% 1.17/1.42          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 1.17/1.42      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.17/1.42  thf('22', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((X0) != (k4_tarski @ X2 @ X1))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X3 @ X0)) = (X3))
% 1.17/1.42          | ~ (r2_hidden @ X1 @ (k2_tarski @ X3 @ X0))
% 1.17/1.42          | ((k2_tarski @ X3 @ X0) = (k1_xboole_0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['20', '21'])).
% 1.17/1.42  thf('23', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((k2_tarski @ X3 @ (k4_tarski @ X2 @ X1)) = (k1_xboole_0))
% 1.17/1.42          | ~ (r2_hidden @ X1 @ (k2_tarski @ X3 @ (k4_tarski @ X2 @ X1)))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X3 @ (k4_tarski @ X2 @ X1))) = (X3)))),
% 1.17/1.42      inference('simplify', [status(thm)], ['22'])).
% 1.17/1.42  thf('24', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 1.17/1.42      inference('demod', [status(thm)], ['17', '18'])).
% 1.17/1.42  thf('25', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((sk_B @ (k2_tarski @ X3 @ (k4_tarski @ X2 @ X1))) = (X3))
% 1.17/1.42          | ~ (r2_hidden @ X1 @ (k2_tarski @ X3 @ (k4_tarski @ X2 @ X1))))),
% 1.17/1.42      inference('clc', [status(thm)], ['23', '24'])).
% 1.17/1.42  thf('26', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         ((sk_B @ (k2_tarski @ X0 @ (k4_tarski @ X1 @ X0))) = (X0))),
% 1.17/1.42      inference('sup-', [status(thm)], ['1', '25'])).
% 1.17/1.42  thf(t51_mcart_1, conjecture,
% 1.17/1.42    (![A:$i,B:$i,C:$i]:
% 1.17/1.42     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42          ( ~( ![D:$i]:
% 1.17/1.42               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.17/1.42                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 1.17/1.42                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 1.17/1.42                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 1.17/1.42  thf(zf_stmt_0, negated_conjecture,
% 1.17/1.42    (~( ![A:$i,B:$i,C:$i]:
% 1.17/1.42        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42             ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42             ( ~( ![D:$i]:
% 1.17/1.42                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.17/1.42                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 1.17/1.42                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 1.17/1.42                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 1.17/1.42    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 1.17/1.42  thf('27', plain,
% 1.17/1.42      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 1.17/1.42        | ((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 1.17/1.42        | ((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.42  thf('28', plain,
% 1.17/1.42      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('split', [status(esa)], ['27'])).
% 1.17/1.42  thf('29', plain,
% 1.17/1.42      ((m1_subset_1 @ sk_D_2 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 1.17/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.42  thf(t48_mcart_1, axiom,
% 1.17/1.42    (![A:$i,B:$i,C:$i]:
% 1.17/1.42     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42          ( ( C ) != ( k1_xboole_0 ) ) & 
% 1.17/1.42          ( ~( ![D:$i]:
% 1.17/1.42               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 1.17/1.42                 ( ( D ) =
% 1.17/1.42                   ( k3_mcart_1 @
% 1.17/1.42                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 1.17/1.42                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 1.17/1.42                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 1.17/1.42  thf('30', plain,
% 1.17/1.42      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.17/1.42         (((X24) = (k1_xboole_0))
% 1.17/1.42          | ((X25) = (k1_xboole_0))
% 1.17/1.42          | ((X27)
% 1.17/1.42              = (k3_mcart_1 @ (k5_mcart_1 @ X24 @ X25 @ X26 @ X27) @ 
% 1.17/1.42                 (k6_mcart_1 @ X24 @ X25 @ X26 @ X27) @ 
% 1.17/1.42                 (k7_mcart_1 @ X24 @ X25 @ X26 @ X27)))
% 1.17/1.42          | ~ (m1_subset_1 @ X27 @ (k3_zfmisc_1 @ X24 @ X25 @ X26))
% 1.17/1.42          | ((X26) = (k1_xboole_0)))),
% 1.17/1.42      inference('cnf', [status(esa)], [t48_mcart_1])).
% 1.17/1.42  thf('31', plain,
% 1.17/1.42      ((((sk_C) = (k1_xboole_0))
% 1.17/1.42        | ((sk_D_2)
% 1.17/1.42            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 1.17/1.42        | ((sk_B_1) = (k1_xboole_0))
% 1.17/1.42        | ((sk_A) = (k1_xboole_0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['29', '30'])).
% 1.17/1.42  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 1.17/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.42  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.17/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.42  thf('34', plain, (((sk_C) != (k1_xboole_0))),
% 1.17/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.17/1.42  thf('35', plain,
% 1.17/1.42      (((sk_D_2)
% 1.17/1.42         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.17/1.42  thf('36', plain,
% 1.17/1.42      ((((sk_D_2)
% 1.17/1.42          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42             sk_D_2 @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))
% 1.17/1.42         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup+', [status(thm)], ['28', '35'])).
% 1.17/1.42  thf('37', plain,
% 1.17/1.42      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 1.17/1.42         (((X7) != (X6))
% 1.17/1.42          | (r2_hidden @ X7 @ X8)
% 1.17/1.42          | ((X8) != (k2_tarski @ X9 @ X6)))),
% 1.17/1.42      inference('cnf', [status(esa)], [d2_tarski])).
% 1.17/1.42  thf('38', plain,
% 1.17/1.42      (![X6 : $i, X9 : $i]: (r2_hidden @ X6 @ (k2_tarski @ X9 @ X6))),
% 1.17/1.42      inference('simplify', [status(thm)], ['37'])).
% 1.17/1.42  thf(d3_mcart_1, axiom,
% 1.17/1.42    (![A:$i,B:$i,C:$i]:
% 1.17/1.42     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 1.17/1.42  thf('39', plain,
% 1.17/1.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 1.17/1.42           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 1.17/1.42      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.17/1.42  thf('40', plain,
% 1.17/1.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.17/1.42         (((X28) = (k1_xboole_0))
% 1.17/1.42          | ~ (r2_hidden @ X30 @ X28)
% 1.17/1.42          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 1.17/1.42      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.17/1.42  thf('41', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((sk_B @ X3) != (k3_mcart_1 @ X2 @ X1 @ X0))
% 1.17/1.42          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X3)
% 1.17/1.42          | ((X3) = (k1_xboole_0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['39', '40'])).
% 1.17/1.42  thf('42', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((k2_tarski @ X2 @ (k4_tarski @ X1 @ X0)) = (k1_xboole_0))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X2 @ (k4_tarski @ X1 @ X0)))
% 1.17/1.42              != (k3_mcart_1 @ X1 @ X0 @ X3)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['38', '41'])).
% 1.17/1.42  thf('43', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 1.17/1.42      inference('demod', [status(thm)], ['17', '18'])).
% 1.17/1.42  thf('44', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         ((sk_B @ (k2_tarski @ X2 @ (k4_tarski @ X1 @ X0)))
% 1.17/1.42           != (k3_mcart_1 @ X1 @ X0 @ X3))),
% 1.17/1.42      inference('clc', [status(thm)], ['42', '43'])).
% 1.17/1.42  thf('45', plain,
% 1.17/1.42      ((![X0 : $i]:
% 1.17/1.42          ((sk_B @ 
% 1.17/1.42            (k2_tarski @ X0 @ 
% 1.17/1.42             (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ sk_D_2)))
% 1.17/1.42            != (sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup-', [status(thm)], ['36', '44'])).
% 1.17/1.42  thf('46', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X0))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 1.17/1.42      inference('clc', [status(thm)], ['5', '19'])).
% 1.17/1.42  thf('47', plain,
% 1.17/1.42      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 1.17/1.42      inference('simplify', [status(thm)], ['0'])).
% 1.17/1.42  thf('48', plain,
% 1.17/1.42      ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('split', [status(esa)], ['27'])).
% 1.17/1.42  thf('49', plain,
% 1.17/1.42      (((sk_D_2)
% 1.17/1.42         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.17/1.42  thf('50', plain,
% 1.17/1.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 1.17/1.42           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 1.17/1.42      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.17/1.42  thf('51', plain,
% 1.17/1.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.17/1.42         (((X28) = (k1_xboole_0))
% 1.17/1.42          | ~ (r2_hidden @ X29 @ X28)
% 1.17/1.42          | ((sk_B @ X28) != (k4_tarski @ X30 @ X29)))),
% 1.17/1.42      inference('cnf', [status(esa)], [t9_mcart_1])).
% 1.17/1.42  thf('52', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((sk_B @ X3) != (k3_mcart_1 @ X2 @ X1 @ X0))
% 1.17/1.42          | ~ (r2_hidden @ X0 @ X3)
% 1.17/1.42          | ((X3) = (k1_xboole_0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['50', '51'])).
% 1.17/1.42  thf('53', plain,
% 1.17/1.42      (![X0 : $i]:
% 1.17/1.42         (((sk_B @ X0) != (sk_D_2))
% 1.17/1.42          | ((X0) = (k1_xboole_0))
% 1.17/1.42          | ~ (r2_hidden @ (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ X0))),
% 1.17/1.42      inference('sup-', [status(thm)], ['49', '52'])).
% 1.17/1.42  thf('54', plain,
% 1.17/1.42      ((![X0 : $i]:
% 1.17/1.42          (~ (r2_hidden @ sk_D_2 @ X0)
% 1.17/1.42           | ((X0) = (k1_xboole_0))
% 1.17/1.42           | ((sk_B @ X0) != (sk_D_2))))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup-', [status(thm)], ['48', '53'])).
% 1.17/1.42  thf('55', plain,
% 1.17/1.42      ((![X0 : $i]:
% 1.17/1.42          (((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2))
% 1.17/1.42           | ((k2_tarski @ sk_D_2 @ X0) = (k1_xboole_0))))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup-', [status(thm)], ['47', '54'])).
% 1.17/1.42  thf('56', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 1.17/1.42      inference('demod', [status(thm)], ['17', '18'])).
% 1.17/1.42  thf('57', plain,
% 1.17/1.42      ((![X0 : $i]: ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('clc', [status(thm)], ['55', '56'])).
% 1.17/1.42  thf('58', plain,
% 1.17/1.42      ((![X0 : $i]:
% 1.17/1.42          (((X0) != (sk_D_2)) | ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) = (sk_D_2))))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup-', [status(thm)], ['46', '57'])).
% 1.17/1.42  thf('59', plain,
% 1.17/1.42      ((((sk_B @ (k2_tarski @ sk_D_2 @ sk_D_2)) = (sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('simplify', [status(thm)], ['58'])).
% 1.17/1.42  thf('60', plain,
% 1.17/1.42      ((![X0 : $i]: ((sk_B @ (k2_tarski @ sk_D_2 @ X0)) != (sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('clc', [status(thm)], ['55', '56'])).
% 1.17/1.42  thf('61', plain,
% 1.17/1.42      (~ (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 1.17/1.42  thf('62', plain,
% 1.17/1.42      ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('split', [status(esa)], ['27'])).
% 1.17/1.42  thf('63', plain,
% 1.17/1.42      (((sk_D_2)
% 1.17/1.42         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.17/1.42  thf('64', plain,
% 1.17/1.42      ((((sk_D_2)
% 1.17/1.42          = (k3_mcart_1 @ sk_D_2 @ 
% 1.17/1.42             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42             (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))
% 1.17/1.42         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup+', [status(thm)], ['62', '63'])).
% 1.17/1.42  thf('65', plain,
% 1.17/1.42      (((sk_D_2)
% 1.17/1.42         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.17/1.42  thf('66', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         (((sk_B @ (k2_tarski @ X1 @ X0)) = (X0))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X1 @ X0)) = (X1)))),
% 1.17/1.42      inference('clc', [status(thm)], ['5', '19'])).
% 1.17/1.42  thf('67', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         ((sk_B @ (k2_tarski @ X2 @ (k4_tarski @ X1 @ X0)))
% 1.17/1.42           != (k3_mcart_1 @ X1 @ X0 @ X3))),
% 1.17/1.42      inference('clc', [status(thm)], ['42', '43'])).
% 1.17/1.42  thf('68', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ X0 @ (k4_tarski @ X3 @ X2)))
% 1.17/1.42              = (k4_tarski @ X3 @ X2)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['66', '67'])).
% 1.17/1.42  thf('69', plain,
% 1.17/1.42      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         ((sk_B @ 
% 1.17/1.42           (k2_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1) @ (k4_tarski @ X3 @ X2)))
% 1.17/1.42           = (k4_tarski @ X3 @ X2))),
% 1.17/1.42      inference('simplify', [status(thm)], ['68'])).
% 1.17/1.42  thf('70', plain,
% 1.17/1.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 1.17/1.42           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 1.17/1.42      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.17/1.42  thf('71', plain,
% 1.17/1.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 1.17/1.42           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 1.17/1.42      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.17/1.42  thf('72', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ (k4_tarski @ X2 @ X1) @ X0 @ X3)
% 1.17/1.42           = (k4_tarski @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X3))),
% 1.17/1.42      inference('sup+', [status(thm)], ['70', '71'])).
% 1.17/1.42  thf('73', plain,
% 1.17/1.42      (![X6 : $i, X9 : $i]: (r2_hidden @ X9 @ (k2_tarski @ X9 @ X6))),
% 1.17/1.42      inference('simplify', [status(thm)], ['0'])).
% 1.17/1.42  thf('74', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((sk_B @ X3) != (k3_mcart_1 @ X2 @ X1 @ X0))
% 1.17/1.42          | ~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ X3)
% 1.17/1.42          | ((X3) = (k1_xboole_0)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['39', '40'])).
% 1.17/1.42  thf('75', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         (((k2_tarski @ (k4_tarski @ X2 @ X1) @ X0) = (k1_xboole_0))
% 1.17/1.42          | ((sk_B @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X0))
% 1.17/1.42              != (k3_mcart_1 @ X2 @ X1 @ X3)))),
% 1.17/1.42      inference('sup-', [status(thm)], ['73', '74'])).
% 1.17/1.42  thf('76', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]: ((k1_xboole_0) != (k2_tarski @ X1 @ X0))),
% 1.17/1.42      inference('demod', [status(thm)], ['17', '18'])).
% 1.17/1.42  thf('77', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.17/1.42         ((sk_B @ (k2_tarski @ (k4_tarski @ X2 @ X1) @ X0))
% 1.17/1.42           != (k3_mcart_1 @ X2 @ X1 @ X3))),
% 1.17/1.42      inference('clc', [status(thm)], ['75', '76'])).
% 1.17/1.42  thf('78', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.17/1.42         ((sk_B @ 
% 1.17/1.42           (k2_tarski @ (k3_mcart_1 @ (k4_tarski @ X3 @ X2) @ X1 @ X0) @ X5))
% 1.17/1.42           != (k3_mcart_1 @ (k3_mcart_1 @ X3 @ X2 @ X1) @ X0 @ X4))),
% 1.17/1.42      inference('sup-', [status(thm)], ['72', '77'])).
% 1.17/1.42  thf('79', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.42         ((k4_tarski @ (k4_tarski @ X2 @ X1) @ X0)
% 1.17/1.42           != (k3_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X4 @ X3))),
% 1.17/1.42      inference('sup-', [status(thm)], ['69', '78'])).
% 1.17/1.42  thf('80', plain,
% 1.17/1.42      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ X18 @ X19 @ X20)
% 1.17/1.42           = (k4_tarski @ (k4_tarski @ X18 @ X19) @ X20))),
% 1.17/1.42      inference('cnf', [status(esa)], [d3_mcart_1])).
% 1.17/1.42  thf('81', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ X2 @ X1 @ X0)
% 1.17/1.42           != (k3_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0) @ X4 @ X3))),
% 1.17/1.42      inference('demod', [status(thm)], ['79', '80'])).
% 1.17/1.42  thf('82', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]:
% 1.17/1.42         ((k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42           (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42           (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))
% 1.17/1.42           != (k3_mcart_1 @ sk_D_2 @ X1 @ X0))),
% 1.17/1.42      inference('sup-', [status(thm)], ['65', '81'])).
% 1.17/1.42  thf('83', plain,
% 1.17/1.42      (((sk_D_2)
% 1.17/1.42         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ 
% 1.17/1.42            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify_reflect-', [status(thm)], ['31', '32', '33', '34'])).
% 1.17/1.42  thf('84', plain,
% 1.17/1.42      (![X0 : $i, X1 : $i]: ((sk_D_2) != (k3_mcart_1 @ sk_D_2 @ X1 @ X0))),
% 1.17/1.42      inference('demod', [status(thm)], ['82', '83'])).
% 1.17/1.42  thf('85', plain,
% 1.17/1.42      ((((sk_D_2) != (sk_D_2)))
% 1.17/1.42         <= ((((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))))),
% 1.17/1.42      inference('sup-', [status(thm)], ['64', '84'])).
% 1.17/1.42  thf('86', plain,
% 1.17/1.42      (~ (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('simplify', [status(thm)], ['85'])).
% 1.17/1.42  thf('87', plain,
% 1.17/1.42      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 1.17/1.42       (((sk_D_2) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2))) | 
% 1.17/1.42       (((sk_D_2) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('split', [status(esa)], ['27'])).
% 1.17/1.42  thf('88', plain,
% 1.17/1.42      ((((sk_D_2) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2)))),
% 1.17/1.42      inference('sat_resolution*', [status(thm)], ['61', '86', '87'])).
% 1.17/1.42  thf('89', plain,
% 1.17/1.42      (![X0 : $i]:
% 1.17/1.42         ((sk_B @ 
% 1.17/1.42           (k2_tarski @ X0 @ 
% 1.17/1.42            (k4_tarski @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_2) @ sk_D_2)))
% 1.17/1.42           != (sk_D_2))),
% 1.17/1.42      inference('simpl_trail', [status(thm)], ['45', '88'])).
% 1.17/1.42  thf('90', plain, (((sk_D_2) != (sk_D_2))),
% 1.17/1.42      inference('sup-', [status(thm)], ['26', '89'])).
% 1.17/1.42  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 1.17/1.42  
% 1.17/1.42  % SZS output end Refutation
% 1.17/1.42  
% 1.27/1.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
