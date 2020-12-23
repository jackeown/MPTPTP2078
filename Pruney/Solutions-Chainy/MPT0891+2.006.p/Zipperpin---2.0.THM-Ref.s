%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FdjDsQ9LRg

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 240 expanded)
%              Number of leaves         :   30 (  83 expanded)
%              Depth                    :   24
%              Number of atoms          :  865 (3565 expanded)
%              Number of equality atoms :  127 ( 551 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

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

thf('0',plain,(
    ! [X36: $i] :
      ( ( X36 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X36 ) @ X36 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( X19 = X16 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19 = X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_tarski @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( X17 != X16 )
      | ( r2_hidden @ X17 @ X18 )
      | ( X18
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ),
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

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( X41 = k1_xboole_0 )
      | ( X43
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k6_mcart_1 @ X40 @ X41 @ X42 @ X43 ) @ ( k7_mcart_1 @ X40 @ X41 @ X42 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X43 @ ( k3_zfmisc_1 @ X40 @ X41 @ X42 ) )
      | ( X42 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('8',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf('13',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf(d3_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_mcart_1 @ A @ B @ C )
      = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ) )).

thf('14',plain,(
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

thf('15',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_mcart_1 @ ( k3_mcart_1 @ X2 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k2_mcart_1 @ sk_D )
    = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['19'])).

thf('22',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','9','10','11'])).

thf('23',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_D ) )
   <= ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
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

thf('25',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k2_mcart_1 @ X33 ) )
      | ( X33
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t20_mcart_1])).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != ( k2_mcart_1 @ ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X44: $i,X46: $i] :
      ( ( k2_mcart_1 @ ( k4_tarski @ X44 @ X46 ) )
      = X46 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('28',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_tarski @ X34 @ X35 )
     != X35 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_mcart_1 @ X2 @ X1 @ X0 )
     != X0 ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    sk_D
 != ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('32',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('33',plain,
    ( ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['19'])).

thf('34',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('35',plain,
    ( ( sk_D
      = ( k3_mcart_1 @ sk_D @ ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k2_mcart_1 @ sk_D ) ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X38 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( sk_B @ X0 )
         != sk_D )
        | ~ ( r2_hidden @ sk_D @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( ( k1_tarski @ sk_D )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_tarski @ sk_D ) )
       != sk_D ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('39',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ X25 @ ( k1_tarski @ X24 ) )
       != X25 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X16: $i] :
      ( r2_hidden @ X16 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( sk_B @ ( k1_tarski @ sk_D ) )
     != sk_D )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['38','47'])).

thf('49',plain,
    ( ( ( sk_D != sk_D )
      | ( ( k1_tarski @ sk_D )
        = k1_xboole_0 ) )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( sk_D
      = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) )
    | ( sk_D
      = ( k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ) ),
    inference(split,[status(esa)],['19'])).

thf('55',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['30','53','54'])).

thf('56',plain,
    ( sk_D
    = ( k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['20','55'])).

thf('57',plain,
    ( sk_D
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) @ sk_D @ ( k2_mcart_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['18','56'])).

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( X36 = k1_xboole_0 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( ( sk_B @ X36 )
       != ( k3_mcart_1 @ X38 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != sk_D )
      | ~ ( r2_hidden @ sk_D @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_tarski @ sk_D )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k1_tarski @ sk_D ) )
     != sk_D ) ),
    inference('sup-',[status(thm)],['5','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('62',plain,(
    ( sk_B @ ( k1_tarski @ sk_D ) )
 != sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_D != sk_D )
    | ( ( k1_tarski @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','62'])).

thf('64',plain,
    ( ( k1_tarski @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('66',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FdjDsQ9LRg
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:46:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 120 iterations in 0.051s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.52  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.21/0.52  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.21/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.52  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.52  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.52  thf(t29_mcart_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ![B:$i]:
% 0.21/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.52                 ( ![C:$i,D:$i,E:$i]:
% 0.21/0.52                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.52                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X36 : $i]:
% 0.21/0.52         (((X36) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X36) @ X36))),
% 0.21/0.52      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.52  thf(d1_tarski, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X19 @ X18)
% 0.21/0.52          | ((X19) = (X16))
% 0.21/0.52          | ((X18) != (k1_tarski @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X16 : $i, X19 : $i]:
% 0.21/0.52         (((X19) = (X16)) | ~ (r2_hidden @ X19 @ (k1_tarski @ X16)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.52          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.52         (((X17) != (X16))
% 0.21/0.52          | (r2_hidden @ X17 @ X18)
% 0.21/0.52          | ((X18) != (k1_tarski @ X16)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.21/0.52  thf('5', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf(t51_mcart_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ~( ![D:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.52                 ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.52                   ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.52                   ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52             ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52             ( ~( ![D:$i]:
% 0.21/0.52                  ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.52                    ( ( ( D ) != ( k5_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.52                      ( ( D ) != ( k6_mcart_1 @ A @ B @ C @ D ) ) & 
% 0.21/0.52                      ( ( D ) != ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t51_mcart_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      ((m1_subset_1 @ sk_D @ (k3_zfmisc_1 @ sk_A @ sk_B_1 @ sk_C_1))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t48_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.52          ( ~( ![D:$i]:
% 0.21/0.52               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.21/0.52                 ( ( D ) =
% 0.21/0.52                   ( k3_mcart_1 @
% 0.21/0.52                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.52                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.21/0.52                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.21/0.52         (((X40) = (k1_xboole_0))
% 0.21/0.52          | ((X41) = (k1_xboole_0))
% 0.21/0.52          | ((X43)
% 0.21/0.52              = (k3_mcart_1 @ (k5_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.21/0.52                 (k6_mcart_1 @ X40 @ X41 @ X42 @ X43) @ 
% 0.21/0.52                 (k7_mcart_1 @ X40 @ X41 @ X42 @ X43)))
% 0.21/0.52          | ~ (m1_subset_1 @ X43 @ (k3_zfmisc_1 @ X40 @ X41 @ X42))
% 0.21/0.52          | ((X42) = (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((((sk_C_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_D)
% 0.21/0.52            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52               (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52               (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.52        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.52  thf('9', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('11', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 0.21/0.52  thf(d3_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( k3_mcart_1 @ A @ B @ C ) = ( k4_tarski @ ( k4_tarski @ A @ B ) @ C ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.52         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.21/0.52           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.52  thf(t7_mcart_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.52       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_mcart_1 @ (k3_mcart_1 @ X2 @ X1 @ X0)) = (X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['14', '15'])).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (((k2_mcart_1 @ sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '16'])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.21/0.52        | ((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.21/0.52        | ((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.52         <= ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.52         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['8', '9', '10', '11'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      ((((sk_D)
% 0.21/0.52          = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_D)))
% 0.21/0.52         <= ((((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.52         ((k3_mcart_1 @ X27 @ X28 @ X29)
% 0.21/0.52           = (k4_tarski @ (k4_tarski @ X27 @ X28) @ X29))),
% 0.21/0.52      inference('cnf', [status(esa)], [d3_mcart_1])).
% 0.21/0.52  thf(t20_mcart_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( ?[B:$i,C:$i]: ( ( A ) = ( k4_tarski @ B @ C ) ) ) =>
% 0.21/0.52       ( ( ( A ) != ( k1_mcart_1 @ A ) ) & ( ( A ) != ( k2_mcart_1 @ A ) ) ) ))).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.52         (((X33) != (k2_mcart_1 @ X33)) | ((X33) != (k4_tarski @ X34 @ X35)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t20_mcart_1])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X34 : $i, X35 : $i]:
% 0.21/0.52         ((k4_tarski @ X34 @ X35) != (k2_mcart_1 @ (k4_tarski @ X34 @ X35)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X44 : $i, X46 : $i]: ((k2_mcart_1 @ (k4_tarski @ X44 @ X46)) = (X46))),
% 0.21/0.52      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.52  thf('28', plain, (![X34 : $i, X35 : $i]: ((k4_tarski @ X34 @ X35) != (X35))),
% 0.21/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]: ((k3_mcart_1 @ X2 @ X1 @ X0) != (X0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['24', '28'])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (~ (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('simplify_reflect-', [status(thm)], ['23', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.52          | ((sk_B @ (k1_tarski @ X0)) = (X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.52  thf('32', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 0.21/0.52            (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      ((((sk_D)
% 0.21/0.52          = (k3_mcart_1 @ sk_D @ 
% 0.21/0.52             (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ (k2_mcart_1 @ sk_D))))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.52         (((X36) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X38 @ X36)
% 0.21/0.52          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      ((![X0 : $i]:
% 0.21/0.52          (((sk_B @ X0) != (sk_D))
% 0.21/0.52           | ~ (r2_hidden @ sk_D @ X0)
% 0.21/0.52           | ((X0) = (k1_xboole_0))))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      (((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.21/0.52         | ((sk_B @ (k1_tarski @ sk_D)) != (sk_D))))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '37'])).
% 0.21/0.52  thf(t3_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.52  thf('39', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.52  thf(t48_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      (![X2 : $i, X3 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.21/0.52           = (k3_xboole_0 @ X2 @ X3))),
% 0.21/0.52      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.52  thf('41', plain,
% 0.21/0.52      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.52  thf(t2_boole, axiom,
% 0.21/0.52    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t2_boole])).
% 0.21/0.52  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.52  thf(t65_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.52       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i]:
% 0.21/0.52         (~ (r2_hidden @ X24 @ X25)
% 0.21/0.52          | ((k4_xboole_0 @ X25 @ (k1_tarski @ X24)) != (X25)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((k1_xboole_0) != (k1_tarski @ X0))
% 0.21/0.52          | ~ (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.52  thf('46', plain, (![X16 : $i]: (r2_hidden @ X16 @ (k1_tarski @ X16))),
% 0.21/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.52  thf('47', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain,
% 0.21/0.52      ((((sk_B @ (k1_tarski @ sk_D)) != (sk_D)))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('clc', [status(thm)], ['38', '47'])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((((sk_D) != (sk_D)) | ((k1_tarski @ sk_D) = (k1_xboole_0))))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['31', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      ((((k1_tarski @ sk_D) = (k1_xboole_0)))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.52  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('52', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.21/0.52         <= ((((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))))),
% 0.21/0.52      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      (~ (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.21/0.52       (((sk_D) = (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))) | 
% 0.21/0.52       (((sk_D) = (k7_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['19'])).
% 0.21/0.52  thf('55', plain, ((((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['30', '53', '54'])).
% 0.21/0.52  thf('56', plain, (((sk_D) = (k6_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D))),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['20', '55'])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (((sk_D)
% 0.21/0.52         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D) @ sk_D @ 
% 0.21/0.52            (k2_mcart_1 @ sk_D)))),
% 0.21/0.52      inference('demod', [status(thm)], ['18', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.52         (((X36) = (k1_xboole_0))
% 0.21/0.52          | ~ (r2_hidden @ X37 @ X36)
% 0.21/0.52          | ((sk_B @ X36) != (k3_mcart_1 @ X38 @ X37 @ X39)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i]:
% 0.21/0.52         (((sk_B @ X0) != (sk_D))
% 0.21/0.52          | ~ (r2_hidden @ sk_D @ X0)
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      ((((k1_tarski @ sk_D) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B @ (k1_tarski @ sk_D)) != (sk_D)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '59'])).
% 0.21/0.52  thf('61', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('62', plain, (((sk_B @ (k1_tarski @ sk_D)) != (sk_D))),
% 0.21/0.52      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      ((((sk_D) != (sk_D)) | ((k1_tarski @ sk_D) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['3', '62'])).
% 0.21/0.52  thf('64', plain, (((k1_tarski @ sk_D) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['63'])).
% 0.21/0.52  thf('65', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.21/0.52      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('66', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.52  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
