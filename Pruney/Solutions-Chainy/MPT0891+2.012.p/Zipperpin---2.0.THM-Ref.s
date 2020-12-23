%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDG0laGbi7

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:34 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 312 expanded)
%              Number of leaves         :   38 ( 109 expanded)
%              Depth                    :   26
%              Number of atoms          : 1315 (4318 expanded)
%              Number of equality atoms :  180 ( 623 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

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

thf(zf_stmt_3,negated_conjecture,(
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

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('11',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('14',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('18',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_mcart_1 @ sk_D )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','20'])).

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

thf('22',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['11','12','13','14'])).

thf('28',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k3_mcart_1 @ X27 @ X28 @ X29 )
      = ( k4_tarski @ ( k4_tarski @ X27 @ X28 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_mcart_1])).

thf(t20_mcart_1,axiom,(
    ! [A: $i] :
      ( ? [B: $i,C: $i] :
          ( A
          = ( k4_tarski @ B @ C ) )
     => ( ( A
         != ( k1_mcart_1 @ A ) )
        & ( A
         != ( k2_mcart_1 @ A ) ) ) ) )).

thf('30',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k2_mcart_1 @ X33 ) )
      | ( X33
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('31',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != ( k2_mcart_1 @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('33',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X35 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('37',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X9 )
      | ( X6 = X7 )
      | ( X6 = X8 )
      | ( X6 = X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('38',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('40',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X11: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( zip_tseitin_0 @ X15 @ X11 @ X12 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ ( sk_B @ ( k2_tarski @ X0 @ X0 ) ) @ X0 @ X0 @ X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('51',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ ( k1_tarski @ X26 ) )
        = X25 )
      | ( r2_hidden @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('52',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','57'])).

thf('59',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['24'])).

thf('60',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('61',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ sk_D @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D )
        | ~ ( r2_hidden @ sk_D @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( ( k1_tarski @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ sk_D @ sk_D ) )
       != sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('66',plain,
    ( ( ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ sk_D @ sk_D ) )
       != sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( ( sk_B @ ( k2_tarski @ sk_D @ sk_D ) )
       != sk_D )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( sk_D != sk_D )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','67'])).

thf('69',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,
    ( ( ( sk_D != sk_D )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 )
      | ( ( k2_tarski @ sk_D @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_tarski @ sk_D @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('73',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ X25 @ ( k1_tarski @ X24 ) )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
         != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( X0 != X0 )
        | ~ ( r2_hidden @ sk_D @ X0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_D @ X0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['36','78'])).

thf('80',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['24'])).

thf('81',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['35','79','80'])).

thf('82',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['25','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ sk_D @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','82'])).

thf('84',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_D ) )
     != sk_D ) ),
    inference('sup-',[status(thm)],['8','83'])).

thf('85',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('86',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('88',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('90',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ X25 @ ( k1_tarski @ X24 ) )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) )
      | ( k1_xboole_0
       != ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('94',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( k2_tarski @ sk_D @ sk_D )
      = k1_xboole_0 )
    | ( sk_D != sk_D ) ),
    inference(demod,[status(thm)],['84','85','86','96'])).

thf('98',plain,
    ( ( k2_tarski @ sk_D @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
       != X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('103',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    $false ),
    inference(simplify,[status(thm)],['104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iDG0laGbi7
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.54  % Solved by: fo/fo7.sh
% 0.34/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.54  % done 191 iterations in 0.075s
% 0.34/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.54  % SZS output start Refutation
% 0.34/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.34/0.54  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.34/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.54  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.34/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.34/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.34/0.54  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.34/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.34/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.34/0.54  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.34/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.34/0.54  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.34/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.34/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.54  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.54  thf(t69_enumset1, axiom,
% 0.34/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.34/0.54  thf('0', plain, (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf(t70_enumset1, axiom,
% 0.34/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.34/0.54  thf('1', plain,
% 0.34/0.54      (![X18 : $i, X19 : $i]:
% 0.34/0.54         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.34/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.34/0.54  thf(d1_enumset1, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.34/0.54       ( ![E:$i]:
% 0.34/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.34/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.34/0.54  thf(zf_stmt_1, axiom,
% 0.34/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.34/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.34/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_2, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.34/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.34/0.54       ( ![E:$i]:
% 0.34/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.34/0.54  thf('2', plain,
% 0.34/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.34/0.54         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.34/0.54          | (r2_hidden @ X10 @ X14)
% 0.34/0.54          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.34/0.54  thf('3', plain,
% 0.34/0.54      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.34/0.54         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.34/0.54          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.34/0.54      inference('simplify', [status(thm)], ['2'])).
% 0.34/0.54  thf('4', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.34/0.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.34/0.54      inference('sup+', [status(thm)], ['1', '3'])).
% 0.34/0.54  thf('5', plain,
% 0.34/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.34/0.54         (((X6) != (X5)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.54  thf('6', plain,
% 0.34/0.54      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X5 @ X7 @ X8 @ X5)),
% 0.34/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.34/0.54  thf('7', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.34/0.54  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.34/0.54      inference('sup+', [status(thm)], ['0', '7'])).
% 0.34/0.54  thf(t51_mcart_1, conjecture,
% 0.34/0.54    (![A:$i,B:$i,C:$i]:
% 0.34/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54          ( ~( ![D:$i]:
% 0.34/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.34/0.54                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.34/0.54                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.34/0.54                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.34/0.54  thf(zf_stmt_3, negated_conjecture,
% 0.34/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.34/0.54        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54             ( ~( ![D:$i]:
% 0.34/0.54                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.34/0.54                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.34/0.54                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.34/0.54                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.34/0.54    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.34/0.54  thf('9', plain,
% 0.34/0.54      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.54  thf(t48_mcart_1, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i]:
% 0.34/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54          ( ~( ![D:$i]:
% 0.34/0.54               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.34/0.54                 ( ( D ) =
% 0.34/0.54                   ( k3_mcart_1 @
% 0.34/0.54                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.34/0.54                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.34/0.54                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.34/0.54  thf('10', plain,
% 0.34/0.54      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.34/0.54         (((X40) = (k1_xboole_0))
% 0.34/0.54          | ((X41) = (k1_xboole_0))
% 0.34/0.54          | ((X43)
% 0.34/0.54              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.34/0.54                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.34/0.54                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.34/0.54          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X40 @ X41 @ X42))
% 0.34/0.54          | ((X42) = (k1_xboole_0)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.34/0.54  thf('11', plain,
% 0.34/0.54      ((((sk_C) = (k1_xboole_0))
% 0.34/0.54        | ((sk_D)
% 0.34/0.54            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.34/0.54        | ((sk_B_1) = (k1_xboole_0))
% 0.34/0.54        | ((sk_A) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['9', '10'])).
% 0.34/0.54  thf('12', plain, (((sk_A) != (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.54  thf('13', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.54  thf('14', plain, (((sk_C) != (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.54  thf('15', plain,
% 0.34/0.54      (((sk_D)
% 0.34/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.34/0.54  thf('16', plain,
% 0.34/0.54      (((sk_D)
% 0.34/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.34/0.54  thf(d3_mcart_1, axiom,
% 0.34/0.54    (![A:$i,B:$i,C:$i]:
% 0.34/0.54     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.34/0.54  thf('17', plain,
% 0.34/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.34/0.54         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.34/0.54           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.34/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.34/0.54  thf(t7_mcart_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.34/0.54       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.34/0.54  thf('18', plain,
% 0.34/0.54      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.34/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.54  thf('19', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.34/0.54      inference('sup+', [status(thm)], ['17', '18'])).
% 0.34/0.54  thf('20', plain,
% 0.34/0.54      (((k2_mcart_1 @ sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.34/0.54      inference('sup+', [status(thm)], ['16', '19'])).
% 0.34/0.54  thf('21', plain,
% 0.34/0.54      (((sk_D)
% 0.34/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.34/0.54      inference('demod', [status(thm)], ['15', '20'])).
% 0.34/0.54  thf(t29_mcart_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.34/0.54          ( ![B:$i]:
% 0.34/0.54            ( ~( ( r2_hidden @ B @ A ) & 
% 0.34/0.54                 ( ![C:$i,D:$i,E:$i]:
% 0.34/0.54                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.34/0.54                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.34/0.54  thf('22', plain,
% 0.34/0.54      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.34/0.54         (((X36) = (k1_xboole_0))
% 0.34/0.54          | ~ (r2_hidden @ X37 @ X36)
% 0.34/0.54          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.34/0.54  thf('23', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((sk_B @ X0) != (sk_D))
% 0.34/0.54          | ~ (r2_hidden @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ X0)
% 0.34/0.54          | ((X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.34/0.54  thf('24', plain,
% 0.34/0.54      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))
% 0.34/0.54        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))
% 0.34/0.54        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.34/0.54  thf('25', plain,
% 0.34/0.54      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.34/0.54         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('split', [status(esa)], ['24'])).
% 0.34/0.54  thf('26', plain,
% 0.34/0.54      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.34/0.54         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('split', [status(esa)], ['24'])).
% 0.34/0.54  thf('27', plain,
% 0.34/0.54      (((sk_D)
% 0.34/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['11', '12', '13', '14'])).
% 0.34/0.54  thf('28', plain,
% 0.34/0.54      ((((sk_D)
% 0.34/0.54          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ sk_D)))
% 0.34/0.54         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('sup+', [status(thm)], ['26', '27'])).
% 0.34/0.54  thf('29', plain,
% 0.34/0.54      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.34/0.54         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.34/0.54           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.34/0.54      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.34/0.54  thf(t20_mcart_1, axiom,
% 0.34/0.54    (![A:$i]:
% 0.34/0.54     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.34/0.54       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.34/0.54  thf('30', plain,
% 0.34/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.34/0.54         (((X33) != (k2_mcart_1 @ X33)) | ((X33) != (k4_tarski @ X34 @ X35)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.34/0.54  thf('31', plain,
% 0.34/0.54      (![X34 : $i, X35 : $i]:
% 0.34/0.54         ((k4_tarski @ X34 @ X35) != (k2_mcart_1 @ (k4_tarski @ X34 @ X35)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['30'])).
% 0.34/0.54  thf('32', plain,
% 0.34/0.54      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.34/0.54      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.34/0.54  thf('33', plain, (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X35))),
% 0.34/0.54      inference('demod', [status(thm)], ['31', '32'])).
% 0.34/0.54  thf('34', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['29', '33'])).
% 0.34/0.54  thf('35', plain, (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('simplify_reflect-', [status(thm)], ['28', '34'])).
% 0.34/0.54  thf('36', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.34/0.54  thf('37', plain,
% 0.34/0.54      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.34/0.54         ((zip_tseitin_0 @ X6 @ X7 @ X8 @ X9)
% 0.34/0.54          | ((X6) = (X7))
% 0.34/0.54          | ((X6) = (X8))
% 0.34/0.54          | ((X6) = (X9)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.34/0.54  thf('38', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('39', plain,
% 0.34/0.54      (![X36 : $i]:
% 0.34/0.54         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.34/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.34/0.54  thf('40', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('41', plain,
% 0.34/0.54      (![X18 : $i, X19 : $i]:
% 0.34/0.54         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.34/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.34/0.54  thf('42', plain,
% 0.34/0.54      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X15 @ X14)
% 0.34/0.54          | ~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.34/0.54          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.34/0.54  thf('43', plain,
% 0.34/0.54      (![X11 : $i, X12 : $i, X13 : $i, X15 : $i]:
% 0.34/0.54         (~ (zip_tseitin_0 @ X15 @ X11 @ X12 @ X13)
% 0.34/0.54          | ~ (r2_hidden @ X15 @ (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.34/0.54  thf('44', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.34/0.54          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['41', '43'])).
% 0.34/0.54  thf('45', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.34/0.54          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['40', '44'])).
% 0.34/0.54  thf('46', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['39', '45'])).
% 0.34/0.54  thf('47', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (zip_tseitin_0 @ (sk_B @ (k2_tarski @ X0 @ X0)) @ X0 @ X0 @ X0)
% 0.34/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['38', '46'])).
% 0.34/0.54  thf('48', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))
% 0.34/0.54          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))
% 0.34/0.54          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))
% 0.34/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['37', '47'])).
% 0.34/0.54  thf('49', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.54          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.34/0.54  thf('50', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf(t65_zfmisc_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.34/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.34/0.54  thf('51', plain,
% 0.34/0.54      (![X25 : $i, X26 : $i]:
% 0.34/0.54         (((k4_xboole_0 @ X25 @ (k1_tarski @ X26)) = (X25))
% 0.34/0.54          | (r2_hidden @ X26 @ X25))),
% 0.34/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.54  thf(t3_boole, axiom,
% 0.34/0.54    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.34/0.54  thf('52', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.34/0.54  thf(t48_xboole_1, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.54  thf('53', plain,
% 0.34/0.54      (![X2 : $i, X3 : $i]:
% 0.34/0.54         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.34/0.54           = (k3_xboole_0 @ X2 @ X3))),
% 0.34/0.54      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.34/0.54  thf('54', plain,
% 0.34/0.54      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.34/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.34/0.54  thf(t2_boole, axiom,
% 0.34/0.54    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.54  thf('55', plain,
% 0.34/0.54      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.54      inference('cnf', [status(esa)], [t2_boole])).
% 0.34/0.54  thf('56', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.34/0.54  thf('57', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.54          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.34/0.54      inference('sup+', [status(thm)], ['51', '56'])).
% 0.34/0.54  thf('58', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 0.34/0.54          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup+', [status(thm)], ['50', '57'])).
% 0.34/0.54  thf('59', plain,
% 0.34/0.54      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('split', [status(esa)], ['24'])).
% 0.34/0.54  thf('60', plain,
% 0.34/0.54      (((sk_D)
% 0.34/0.54         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.34/0.54      inference('demod', [status(thm)], ['15', '20'])).
% 0.34/0.54  thf('61', plain,
% 0.34/0.54      ((((sk_D)
% 0.34/0.54          = (k3_mcart_1 @ sk_D @ (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D) @ 
% 0.34/0.54             (k2_mcart_1 @ sk_D))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('sup+', [status(thm)], ['59', '60'])).
% 0.34/0.54  thf('62', plain,
% 0.34/0.54      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.34/0.54         (((X36) = (k1_xboole_0))
% 0.34/0.54          | ~ (r2_hidden @ X38 @ X36)
% 0.34/0.54          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.34/0.54  thf('63', plain,
% 0.34/0.54      ((![X0 : $i]:
% 0.34/0.54          (((sk_B @ X0) != (sk_D))
% 0.34/0.54           | ~ (r2_hidden @ sk_D @ X0)
% 0.34/0.54           | ((X0) = (k1_xboole_0))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.34/0.54  thf('64', plain,
% 0.34/0.54      (((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.34/0.54         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))
% 0.34/0.54         | ((sk_B @ (k2_tarski @ sk_D @ sk_D)) != (sk_D))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['58', '63'])).
% 0.34/0.54  thf('65', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('66', plain,
% 0.34/0.54      (((((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))
% 0.34/0.54         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))
% 0.34/0.54         | ((sk_B @ (k2_tarski @ sk_D @ sk_D)) != (sk_D))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.34/0.54  thf('67', plain,
% 0.34/0.54      (((((sk_B @ (k2_tarski @ sk_D @ sk_D)) != (sk_D))
% 0.34/0.54         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('simplify', [status(thm)], ['66'])).
% 0.34/0.54  thf('68', plain,
% 0.34/0.54      (((((sk_D) != (sk_D))
% 0.34/0.54         | ((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.34/0.54         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['49', '67'])).
% 0.34/0.54  thf('69', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('70', plain,
% 0.34/0.54      (((((sk_D) != (sk_D))
% 0.34/0.54         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))
% 0.34/0.54         | ((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('demod', [status(thm)], ['68', '69'])).
% 0.34/0.54  thf('71', plain,
% 0.34/0.54      ((((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0)))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('simplify', [status(thm)], ['70'])).
% 0.34/0.54  thf('72', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('73', plain,
% 0.34/0.54      (![X24 : $i, X25 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X24 @ X25)
% 0.34/0.54          | ((k4_xboole_0 @ X25 @ (k1_tarski @ X24)) != (X25)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.54  thf('74', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 0.34/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.34/0.54  thf('75', plain,
% 0.34/0.54      ((![X0 : $i]:
% 0.34/0.54          (((k4_xboole_0 @ X0 @ k1_xboole_0) != (X0))
% 0.34/0.54           | ~ (r2_hidden @ sk_D @ X0)))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['71', '74'])).
% 0.34/0.54  thf('76', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.34/0.54      inference('cnf', [status(esa)], [t3_boole])).
% 0.34/0.54  thf('77', plain,
% 0.34/0.54      ((![X0 : $i]: (((X0) != (X0)) | ~ (r2_hidden @ sk_D @ X0)))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('demod', [status(thm)], ['75', '76'])).
% 0.34/0.54  thf('78', plain,
% 0.34/0.54      ((![X0 : $i]: ~ (r2_hidden @ sk_D @ X0))
% 0.34/0.54         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))))),
% 0.34/0.54      inference('simplify', [status(thm)], ['77'])).
% 0.34/0.54  thf('79', plain, (~ (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['36', '78'])).
% 0.34/0.54  thf('80', plain,
% 0.34/0.54      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))) | 
% 0.34/0.54       (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))) | 
% 0.34/0.54       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('split', [status(esa)], ['24'])).
% 0.34/0.54  thf('81', plain, ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D)))),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['35', '79', '80'])).
% 0.34/0.54  thf('82', plain, (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 0.34/0.54      inference('simpl_trail', [status(thm)], ['25', '81'])).
% 0.34/0.54  thf('83', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((sk_B @ X0) != (sk_D))
% 0.34/0.54          | ~ (r2_hidden @ sk_D @ X0)
% 0.34/0.54          | ((X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('demod', [status(thm)], ['23', '82'])).
% 0.34/0.54  thf('84', plain,
% 0.34/0.54      ((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.34/0.54        | ((sk_B @ (k1_tarski @ sk_D)) != (sk_D)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['8', '83'])).
% 0.34/0.54  thf('85', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('86', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('87', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.34/0.54          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.34/0.54  thf('88', plain,
% 0.34/0.54      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.34/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.34/0.54  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.34/0.54  thf('90', plain,
% 0.34/0.54      (![X24 : $i, X25 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X24 @ X25)
% 0.34/0.54          | ((k4_xboole_0 @ X25 @ (k1_tarski @ X24)) != (X25)))),
% 0.34/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.34/0.54  thf('91', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.34/0.54          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['89', '90'])).
% 0.34/0.54  thf('92', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0))
% 0.34/0.54          | ((k1_xboole_0) != (k1_tarski @ X0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['88', '91'])).
% 0.34/0.54  thf('93', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.34/0.54  thf('94', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.34/0.54      inference('demod', [status(thm)], ['92', '93'])).
% 0.34/0.54  thf('95', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.54          | ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['87', '94'])).
% 0.34/0.54  thf('96', plain, (![X0 : $i]: ((sk_B @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.34/0.54      inference('simplify', [status(thm)], ['95'])).
% 0.34/0.54  thf('97', plain,
% 0.34/0.54      ((((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0)) | ((sk_D) != (sk_D)))),
% 0.34/0.54      inference('demod', [status(thm)], ['84', '85', '86', '96'])).
% 0.34/0.54  thf('98', plain, (((k2_tarski @ sk_D @ sk_D) = (k1_xboole_0))),
% 0.34/0.54      inference('simplify', [status(thm)], ['97'])).
% 0.34/0.54  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.34/0.54      inference('demod', [status(thm)], ['54', '55'])).
% 0.34/0.54  thf('100', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) != (X1))
% 0.34/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.34/0.54  thf('101', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (((k1_xboole_0) != (k2_tarski @ X0 @ X0))
% 0.34/0.54          | ~ (r2_hidden @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['99', '100'])).
% 0.34/0.54  thf('102', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.34/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.34/0.54  thf('103', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.34/0.54      inference('demod', [status(thm)], ['101', '102'])).
% 0.34/0.54  thf('104', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['98', '103'])).
% 0.34/0.54  thf('105', plain, ($false), inference('simplify', [status(thm)], ['104'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.34/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
