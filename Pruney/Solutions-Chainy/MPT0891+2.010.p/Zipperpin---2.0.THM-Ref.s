%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iebmzpXWE3

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 601 expanded)
%              Number of leaves         :   40 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          : 1391 (9488 expanded)
%              Number of equality atoms :  196 (1428 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( X9 = X10 )
      | ( X9 = X11 )
      | ( X9 = X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X40: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X40 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k1_enumset1 @ X21 @ X21 @ X22 )
      = ( k2_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ~ ( zip_tseitin_0 @ X18 @ X14 @ X15 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t73_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = k1_xboole_0 )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X27 @ X29 ) @ X28 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t73_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23 != X25 )
      | ~ ( r2_hidden @ X23 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X24 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference(clc,[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_0 @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['8','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X40: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X40 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

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

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('27',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k3_zfmisc_1 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('31',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('35',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('36',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('41',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X47
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X44 @ X45 @ X46 @ X47 ) @ ( k6_mcart_1 @ X44 @ X45 @ X46 @ X47 ) @ ( k7_mcart_1 @ X44 @ X45 @ X46 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k3_zfmisc_1 @ X44 @ X45 @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('42',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('43',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X47
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X44 @ X45 @ X46 @ X47 ) @ ( k6_mcart_1 @ X44 @ X45 @ X46 @ X47 ) @ ( k7_mcart_1 @ X44 @ X45 @ X46 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X47 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) @ X46 ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('46',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k3_zfmisc_1 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('47',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('48',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X50 ) ) )
      | ~ ( m1_subset_1 @ X50 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('51',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('52',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('53',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('54',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['32','33','34','35'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('56',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k3_zfmisc_1 @ X48 @ X49 @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('57',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k3_zfmisc_1 @ X34 @ X35 @ X36 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('58',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X48 = k1_xboole_0 )
      | ( X49 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X48 @ X49 @ X51 @ X50 )
        = ( k2_mcart_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) @ X51 ) )
      | ( X51 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
      = ( k2_mcart_1 @ sk_D_1 ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('62',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('63',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','53','54','63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('67',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('70',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r2_hidden @ X41 @ X40 )
      | ( ( sk_B @ X40 )
       != ( k3_mcart_1 @ X42 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('74',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X2 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['68','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['39','75'])).

thf('77',plain,
    ( $false
   <= ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','76'])).

thf('78',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_mcart_1 @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['59','60','61','62'])).

thf('79',plain,
    ( ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['37'])).

thf('80',plain,
    ( ( sk_D_1
      = ( k2_mcart_1 @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67'])).

thf('82',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k3_mcart_1 @ X31 @ X32 @ X33 )
      = ( k4_tarski @ ( k4_tarski @ X31 @ X32 ) @ X33 ) ) ),
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

thf('84',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( X37
       != ( k2_mcart_1 @ X37 ) )
      | ( X37
       != ( k4_tarski @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('85',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k4_tarski @ X38 @ X39 )
     != ( k2_mcart_1 @ ( k4_tarski @ X38 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('86',plain,(
    ! [X52: $i,X54: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X52 @ X54 ) )
      = X54 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('87',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k4_tarski @ X38 @ X39 )
     != X39 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['83','87'])).

thf('89',plain,(
    sk_D_1
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('simplify_reflect-',[status(thm)],['82','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('91',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['49','50','51','52'])).

thf('92',plain,
    ( ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['37'])).

thf('93',plain,
    ( ( sk_D_1
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,
    ( sk_D_1
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67'])).

thf('95',plain,
    ( ( sk_D_1
      = ( k3_mcart_1 @ sk_D_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_D_1 ) ) @ ( k2_mcart_1 @ sk_D_1 ) ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('97',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( r2_hidden @ X42 @ X40 )
      | ( ( sk_B @ X40 )
       != ( k3_mcart_1 @ X42 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
       != ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','17'])).

thf('101',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ~ ( r2_hidden @ X3 @ ( k1_tarski @ ( k3_mcart_1 @ X3 @ X2 @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
   <= ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['95','101'])).

thf('103',plain,(
    sk_D_1
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['90','102'])).

thf('104',plain,
    ( ( sk_D_1
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) )
    | ( sk_D_1
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference(split,[status(esa)],['37'])).

thf('105',plain,
    ( sk_D_1
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference('sat_resolution*',[status(thm)],['89','103','104'])).

thf('106',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['77','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iebmzpXWE3
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 123 iterations in 0.064s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.51  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(d1_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, axiom,
% 0.20/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.51         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.20/0.51          | ((X9) = (X10))
% 0.20/0.51          | ((X9) = (X11))
% 0.20/0.51          | ((X9) = (X12)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t29_mcart_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.51                 ( ![C:$i,D:$i,E:$i]:
% 0.20/0.51                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.20/0.51                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X40 : $i]:
% 0.20/0.51         (((X40) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X40) @ X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.51  thf(t70_enumset1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i]:
% 0.20/0.51         ((k1_enumset1 @ X21 @ X21 @ X22) = (k2_tarski @ X21 @ X22))),
% 0.20/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.51  thf(t69_enumset1, axiom,
% 0.20/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.51  thf('3', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.51          | ~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.20/0.51          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.20/0.51         (~ (zip_tseitin_0 @ X18 @ X14 @ X15 @ X16)
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.20/0.51          | ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '7'])).
% 0.20/0.51  thf('9', plain, (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.51  thf(t3_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.51  thf('10', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.51  thf(t73_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.51         ((r2_hidden @ X27 @ X28)
% 0.20/0.51          | ((k4_xboole_0 @ (k2_tarski @ X27 @ X29) @ X28) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t73_zfmisc_1])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k2_tarski @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(t4_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.51  thf(t64_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.51       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.51         (((X23) != (X25))
% 0.20/0.51          | ~ (r2_hidden @ X23 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X24 @ (k1_tarski @ X25)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.51  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) != (k1_xboole_0))),
% 0.20/0.51      inference('clc', [status(thm)], ['12', '16'])).
% 0.20/0.51  thf('18', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X0 : $i]: ~ (zip_tseitin_0 @ (sk_B @ (k1_tarski @ X0)) @ X0 @ X0 @ X0)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['8', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.51          | ((sk_B @ (k1_tarski @ X0)) = (X0))
% 0.20/0.51          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '19'])).
% 0.20/0.51  thf('21', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X40 : $i]:
% 0.20/0.51         (((X40) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X40) @ X40))),
% 0.20/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.20/0.51          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf('24', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.51  thf('25', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf(t51_mcart_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ![D:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.51                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.51                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.51                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_3, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.51        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51             ( ~( ![D:$i]:
% 0.20/0.51                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.51                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.51                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.20/0.51                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf(d3_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.20/0.51       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.51        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf(t50_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ![D:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.51                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.51                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.51                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.20/0.51                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.20/0.51                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.51         (((X48) = (k1_xboole_0))
% 0.20/0.51          | ((X49) = (k1_xboole_0))
% 0.20/0.51          | ((k6_mcart_1 @ X48 @ X49 @ X51 @ X50)
% 0.20/0.51              = (k2_mcart_1 @ (k1_mcart_1 @ X50)))
% 0.20/0.51          | ~ (m1_subset_1 @ X50 @ (k3_zfmisc_1 @ X48 @ X49 @ X51))
% 0.20/0.51          | ((X51) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.51         (((X48) = (k1_xboole_0))
% 0.20/0.51          | ((X49) = (k1_xboole_0))
% 0.20/0.51          | ((k6_mcart_1 @ X48 @ X49 @ X51 @ X50)
% 0.20/0.51              = (k2_mcart_1 @ (k1_mcart_1 @ X50)))
% 0.20/0.51          | ~ (m1_subset_1 @ X50 @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49) @ X51))
% 0.20/0.51          | ((X51) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.20/0.51            = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.20/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '31'])).
% 0.20/0.51  thf('33', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('34', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('35', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.20/0.51         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.20/0.51        | ((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))
% 0.20/0.51        | ((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['37'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((sk_D_1) = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.20/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['36', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.51        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf(t48_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ![D:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.20/0.51                 ( ( D ) =
% 0.20/0.51                   ( k3_mcart_1 @
% 0.20/0.51                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.51                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.20/0.51                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.51         (((X44) = (k1_xboole_0))
% 0.20/0.51          | ((X45) = (k1_xboole_0))
% 0.20/0.51          | ((X47)
% 0.20/0.51              = (k3_mcart_1 @ (k5_mcart_1 @ X44 @ X45 @ X46 @ X47) @ 
% 0.20/0.51                 (k6_mcart_1 @ X44 @ X45 @ X46 @ X47) @ 
% 0.20/0.51                 (k7_mcart_1 @ X44 @ X45 @ X46 @ X47)))
% 0.20/0.51          | ~ (m1_subset_1 @ X47 @ (k3_zfmisc_1 @ X44 @ X45 @ X46))
% 0.20/0.51          | ((X46) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.20/0.51         (((X44) = (k1_xboole_0))
% 0.20/0.51          | ((X45) = (k1_xboole_0))
% 0.20/0.51          | ((X47)
% 0.20/0.51              = (k3_mcart_1 @ (k5_mcart_1 @ X44 @ X45 @ X46 @ X47) @ 
% 0.20/0.51                 (k6_mcart_1 @ X44 @ X45 @ X46 @ X47) @ 
% 0.20/0.51                 (k7_mcart_1 @ X44 @ X45 @ X46 @ X47)))
% 0.20/0.51          | ~ (m1_subset_1 @ X47 @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45) @ X46))
% 0.20/0.51          | ((X46) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((sk_D_1)
% 0.20/0.51            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.51               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) @ 
% 0.20/0.51               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.20/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.51        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.51         (((X48) = (k1_xboole_0))
% 0.20/0.51          | ((X49) = (k1_xboole_0))
% 0.20/0.51          | ((k5_mcart_1 @ X48 @ X49 @ X51 @ X50)
% 0.20/0.51              = (k1_mcart_1 @ (k1_mcart_1 @ X50)))
% 0.20/0.51          | ~ (m1_subset_1 @ X50 @ (k3_zfmisc_1 @ X48 @ X49 @ X51))
% 0.20/0.51          | ((X51) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.51         (((X48) = (k1_xboole_0))
% 0.20/0.51          | ((X49) = (k1_xboole_0))
% 0.20/0.51          | ((k5_mcart_1 @ X48 @ X49 @ X51 @ X50)
% 0.20/0.51              = (k1_mcart_1 @ (k1_mcart_1 @ X50)))
% 0.20/0.51          | ~ (m1_subset_1 @ X50 @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49) @ X51))
% 0.20/0.51          | ((X51) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.20/0.51            = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))
% 0.20/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '48'])).
% 0.20/0.51  thf('50', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('51', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('52', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.20/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (((k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.20/0.51         = (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ 
% 0.20/0.51        (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1) @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.51         (((X48) = (k1_xboole_0))
% 0.20/0.51          | ((X49) = (k1_xboole_0))
% 0.20/0.51          | ((k7_mcart_1 @ X48 @ X49 @ X51 @ X50) = (k2_mcart_1 @ X50))
% 0.20/0.51          | ~ (m1_subset_1 @ X50 @ (k3_zfmisc_1 @ X48 @ X49 @ X51))
% 0.20/0.51          | ((X51) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.51         ((k3_zfmisc_1 @ X34 @ X35 @ X36)
% 0.20/0.51           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35) @ X36))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.20/0.51  thf('58', plain,
% 0.20/0.51      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 0.20/0.51         (((X48) = (k1_xboole_0))
% 0.20/0.51          | ((X49) = (k1_xboole_0))
% 0.20/0.51          | ((k7_mcart_1 @ X48 @ X49 @ X51 @ X50) = (k2_mcart_1 @ X50))
% 0.20/0.51          | ~ (m1_subset_1 @ X50 @ 
% 0.20/0.51               (k2_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49) @ X51))
% 0.20/0.51          | ((X51) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))
% 0.20/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['55', '58'])).
% 0.20/0.51  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('61', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('62', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('63', plain,
% 0.20/0.51      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.20/0.51  thf('64', plain,
% 0.20/0.51      ((((sk_C) = (k1_xboole_0))
% 0.20/0.51        | ((sk_D_1)
% 0.20/0.51            = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51               (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))
% 0.20/0.51        | ((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['44', '53', '54', '63'])).
% 0.20/0.51  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('66', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('67', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('68', plain,
% 0.20/0.51      (((sk_D_1)
% 0.20/0.51         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.51  thf('69', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('70', plain,
% 0.20/0.51      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.51         (((X40) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X41 @ X40)
% 0.20/0.51          | ((sk_B @ X40) != (k3_mcart_1 @ X42 @ X41 @ X43)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.51  thf('71', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.20/0.51          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['69', '70'])).
% 0.20/0.51  thf('72', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.51  thf('73', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.51  thf('74', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X2 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.20/0.51  thf('75', plain,
% 0.20/0.51      (~ (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51          (k1_tarski @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['68', '74'])).
% 0.20/0.51  thf('76', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['39', '75'])).
% 0.20/0.51  thf('77', plain,
% 0.20/0.51      (($false)
% 0.20/0.51         <= ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '76'])).
% 0.20/0.51  thf('78', plain,
% 0.20/0.51      (((k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1) = (k2_mcart_1 @ sk_D_1))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['59', '60', '61', '62'])).
% 0.20/0.51  thf('79', plain,
% 0.20/0.51      ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['37'])).
% 0.20/0.51  thf('80', plain,
% 0.20/0.51      ((((sk_D_1) = (k2_mcart_1 @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.51  thf('81', plain,
% 0.20/0.51      (((sk_D_1)
% 0.20/0.51         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.51  thf('82', plain,
% 0.20/0.51      ((((sk_D_1)
% 0.20/0.51          = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51             (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['80', '81'])).
% 0.20/0.51  thf(d3_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.20/0.51  thf('83', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.51         ((k3_mcart_1 @ X31 @ X32 @ X33)
% 0.20/0.51           = (k4_tarski @ (k4_tarski @ X31 @ X32) @ X33))),
% 0.20/0.51      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.20/0.51  thf(t20_mcart_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.20/0.51       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.20/0.51  thf('84', plain,
% 0.20/0.51      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.51         (((X37) != (k2_mcart_1 @ X37)) | ((X37) != (k4_tarski @ X38 @ X39)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.20/0.51  thf('85', plain,
% 0.20/0.51      (![X38 : $i, X39 : $i]:
% 0.20/0.51         ((k4_tarski @ X38 @ X39) != (k2_mcart_1 @ (k4_tarski @ X38 @ X39)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['84'])).
% 0.20/0.51  thf(t7_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.20/0.51       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.20/0.51  thf('86', plain,
% 0.20/0.51      (![X52 : $i, X54 : $i]: ((k2_mcart_1 @ (k4_tarski @ X52 @ X54)) = (X54))),
% 0.20/0.51      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.20/0.51  thf('87', plain, (![X38 : $i, X39 : $i]: ((k4_tarski @ X38 @ X39) != (X39))),
% 0.20/0.51      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.51  thf('88', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['83', '87'])).
% 0.20/0.51  thf('89', plain,
% 0.20/0.51      (~ (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['82', '88'])).
% 0.20/0.51  thf('90', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('91', plain,
% 0.20/0.51      (((k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)
% 0.20/0.51         = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['49', '50', '51', '52'])).
% 0.20/0.51  thf('92', plain,
% 0.20/0.51      ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['37'])).
% 0.20/0.51  thf('93', plain,
% 0.20/0.51      ((((sk_D_1) = (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1))))
% 0.20/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['91', '92'])).
% 0.20/0.51  thf('94', plain,
% 0.20/0.51      (((sk_D_1)
% 0.20/0.51         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51            (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ (k2_mcart_1 @ sk_D_1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['64', '65', '66', '67'])).
% 0.20/0.51  thf('95', plain,
% 0.20/0.51      ((((sk_D_1)
% 0.20/0.51          = (k3_mcart_1 @ sk_D_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_D_1)) @ 
% 0.20/0.51             (k2_mcart_1 @ sk_D_1))))
% 0.20/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['93', '94'])).
% 0.20/0.51  thf('96', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('97', plain,
% 0.20/0.51      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.51         (((X40) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X42 @ X40)
% 0.20/0.51          | ((sk_B @ X40) != (k3_mcart_1 @ X42 @ X41 @ X43)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.20/0.51  thf('98', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (((X0) != (k3_mcart_1 @ X3 @ X2 @ X1))
% 0.20/0.51          | ~ (r2_hidden @ X3 @ (k1_tarski @ X0))
% 0.20/0.51          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.51  thf('99', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (((k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['98'])).
% 0.20/0.51  thf('100', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '17'])).
% 0.20/0.51  thf('101', plain,
% 0.20/0.51      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         ~ (r2_hidden @ X3 @ (k1_tarski @ (k3_mcart_1 @ X3 @ X2 @ X1)))),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['99', '100'])).
% 0.20/0.51  thf('102', plain,
% 0.20/0.51      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1)))
% 0.20/0.51         <= ((((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['95', '101'])).
% 0.20/0.51  thf('103', plain,
% 0.20/0.51      (~ (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['90', '102'])).
% 0.20/0.51  thf('104', plain,
% 0.20/0.51      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.20/0.51       (((sk_D_1) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1))) | 
% 0.20/0.51       (((sk_D_1) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['37'])).
% 0.20/0.51  thf('105', plain,
% 0.20/0.51      ((((sk_D_1) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['89', '103', '104'])).
% 0.20/0.51  thf('106', plain, ($false),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['77', '105'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
