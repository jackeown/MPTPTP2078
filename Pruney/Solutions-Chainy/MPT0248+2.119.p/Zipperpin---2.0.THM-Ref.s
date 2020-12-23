%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LTqVc3lDeS

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:35 EST 2020

% Result     : Theorem 51.51s
% Output     : Refutation 51.51s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 778 expanded)
%              Number of leaves         :   20 ( 210 expanded)
%              Depth                    :   27
%              Number of atoms          : 1258 (9251 expanded)
%              Number of equality atoms :  179 (1194 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X48
        = ( k1_tarski @ X47 ) )
      | ( X48 = k1_xboole_0 )
      | ~ ( r1_tarski @ X48 @ ( k1_tarski @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_C_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('17',plain,(
    ! [X44: $i,X46: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X44 ) @ X46 )
      | ~ ( r2_hidden @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf('24',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('28',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('31',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['25'])).

thf('36',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['27','29','37'])).

thf('39',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['26','38'])).

thf('40',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','39'])).

thf('41',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('42',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r1_tarski @ X48 @ ( k1_tarski @ X49 ) )
      | ( X48 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('45',plain,(
    ! [X49: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X49 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['48'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('56',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ X1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('59',plain,(
    ! [X1: $i,X3: $i,X5: $i] :
      ( ( X5
        = ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X1 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k2_xboole_0 @ ( k1_tarski @ ( sk_D @ X1 @ X1 @ X0 ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('66',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('70',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('71',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['72','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ( ( k2_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('79',plain,(
    ! [X49: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X49 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k2_tarski @ X0 @ X0 ) )
      = ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) @ ( k2_tarski @ X0 @ X0 ) )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['77','82','83'])).

thf('85',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('86',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('90',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('91',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r2_hidden @ X44 @ X45 )
      | ~ ( r1_tarski @ ( k1_tarski @ X44 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup+',[status(thm)],['88','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup+',[status(thm)],['65','96'])).

thf('98',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
        = X1 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) )
      = X0 ) ),
    inference(condensation,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ k1_xboole_0 )
        = ( sk_D @ X0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['64','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ k1_xboole_0 ) @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['47','106'])).

thf('108',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ( ( sk_B @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ k1_xboole_0 )
       != ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( X0
        = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ( ( sk_B @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('112',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','112'])).

thf('114',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('116',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( X0
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['114','117'])).

thf('119',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['26','38'])).

thf('120',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('122',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['113','122'])).

thf('124',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_1 ),
    inference(demod,[status(thm)],['0','123'])).

thf('125',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['26','38'])).

thf('126',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['124','125'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LTqVc3lDeS
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 51.51/51.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 51.51/51.72  % Solved by: fo/fo7.sh
% 51.51/51.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 51.51/51.72  % done 22202 iterations in 51.230s
% 51.51/51.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 51.51/51.72  % SZS output start Refutation
% 51.51/51.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 51.51/51.72  thf(sk_A_type, type, sk_A: $i).
% 51.51/51.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 51.51/51.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 51.51/51.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 51.51/51.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 51.51/51.72  thf(sk_B_type, type, sk_B: $i > $i).
% 51.51/51.72  thf(sk_B_1_type, type, sk_B_1: $i).
% 51.51/51.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 51.51/51.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 51.51/51.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 51.51/51.72  thf(t43_zfmisc_1, conjecture,
% 51.51/51.72    (![A:$i,B:$i,C:$i]:
% 51.51/51.72     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 51.51/51.72          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 51.51/51.72          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 51.51/51.72          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 51.51/51.72  thf(zf_stmt_0, negated_conjecture,
% 51.51/51.72    (~( ![A:$i,B:$i,C:$i]:
% 51.51/51.72        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 51.51/51.72             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 51.51/51.72             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 51.51/51.72             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 51.51/51.72    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 51.51/51.72  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf(t7_xboole_1, axiom,
% 51.51/51.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 51.51/51.72  thf('3', plain,
% 51.51/51.72      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 51.51/51.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.51/51.72  thf('4', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 51.51/51.72      inference('sup+', [status(thm)], ['2', '3'])).
% 51.51/51.72  thf(l3_zfmisc_1, axiom,
% 51.51/51.72    (![A:$i,B:$i]:
% 51.51/51.72     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 51.51/51.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 51.51/51.72  thf('5', plain,
% 51.51/51.72      (![X47 : $i, X48 : $i]:
% 51.51/51.72         (((X48) = (k1_tarski @ X47))
% 51.51/51.72          | ((X48) = (k1_xboole_0))
% 51.51/51.72          | ~ (r1_tarski @ X48 @ (k1_tarski @ X47)))),
% 51.51/51.72      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 51.51/51.72  thf('6', plain,
% 51.51/51.72      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['4', '5'])).
% 51.51/51.72  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf(t7_xboole_0, axiom,
% 51.51/51.72    (![A:$i]:
% 51.51/51.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 51.51/51.72          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 51.51/51.72  thf('8', plain,
% 51.51/51.72      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 51.51/51.72      inference('cnf', [status(esa)], [t7_xboole_0])).
% 51.51/51.72  thf(d3_xboole_0, axiom,
% 51.51/51.72    (![A:$i,B:$i,C:$i]:
% 51.51/51.72     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 51.51/51.72       ( ![D:$i]:
% 51.51/51.72         ( ( r2_hidden @ D @ C ) <=>
% 51.51/51.72           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 51.51/51.72  thf('9', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 51.51/51.72         (~ (r2_hidden @ X0 @ X1)
% 51.51/51.72          | (r2_hidden @ X0 @ X2)
% 51.51/51.72          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 51.51/51.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 51.51/51.72  thf('10', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X3 : $i]:
% 51.51/51.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 51.51/51.72      inference('simplify', [status(thm)], ['9'])).
% 51.51/51.72  thf('11', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X0) = (k1_xboole_0))
% 51.51/51.72          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['8', '10'])).
% 51.51/51.72  thf('12', plain,
% 51.51/51.72      (((r2_hidden @ (sk_B @ sk_C_1) @ (k1_tarski @ sk_A))
% 51.51/51.72        | ((sk_C_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['7', '11'])).
% 51.51/51.72  thf(d1_tarski, axiom,
% 51.51/51.72    (![A:$i,B:$i]:
% 51.51/51.72     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 51.51/51.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 51.51/51.72  thf('13', plain,
% 51.51/51.72      (![X11 : $i, X13 : $i, X14 : $i]:
% 51.51/51.72         (~ (r2_hidden @ X14 @ X13)
% 51.51/51.72          | ((X14) = (X11))
% 51.51/51.72          | ((X13) != (k1_tarski @ X11)))),
% 51.51/51.72      inference('cnf', [status(esa)], [d1_tarski])).
% 51.51/51.72  thf('14', plain,
% 51.51/51.72      (![X11 : $i, X14 : $i]:
% 51.51/51.72         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['13'])).
% 51.51/51.72  thf('15', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B @ sk_C_1) = (sk_A)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['12', '14'])).
% 51.51/51.72  thf('16', plain,
% 51.51/51.72      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 51.51/51.72      inference('cnf', [status(esa)], [t7_xboole_0])).
% 51.51/51.72  thf(l1_zfmisc_1, axiom,
% 51.51/51.72    (![A:$i,B:$i]:
% 51.51/51.72     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 51.51/51.72  thf('17', plain,
% 51.51/51.72      (![X44 : $i, X46 : $i]:
% 51.51/51.72         ((r1_tarski @ (k1_tarski @ X44) @ X46) | ~ (r2_hidden @ X44 @ X46))),
% 51.51/51.72      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 51.51/51.72  thf('18', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['16', '17'])).
% 51.51/51.72  thf('19', plain,
% 51.51/51.72      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 51.51/51.72        | ((sk_C_1) = (k1_xboole_0))
% 51.51/51.72        | ((sk_C_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['15', '18'])).
% 51.51/51.72  thf('20', plain,
% 51.51/51.72      ((((sk_C_1) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))),
% 51.51/51.72      inference('simplify', [status(thm)], ['19'])).
% 51.51/51.72  thf(t12_xboole_1, axiom,
% 51.51/51.72    (![A:$i,B:$i]:
% 51.51/51.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 51.51/51.72  thf('21', plain,
% 51.51/51.72      (![X7 : $i, X8 : $i]:
% 51.51/51.72         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 51.51/51.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 51.51/51.72  thf('22', plain,
% 51.51/51.72      ((((sk_C_1) = (k1_xboole_0))
% 51.51/51.72        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1) = (sk_C_1)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['20', '21'])).
% 51.51/51.72  thf('23', plain,
% 51.51/51.72      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 51.51/51.72        | ((sk_B_1) = (k1_xboole_0))
% 51.51/51.72        | ((sk_C_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['6', '22'])).
% 51.51/51.72  thf('24', plain,
% 51.51/51.72      ((((k1_tarski @ sk_A) = (sk_C_1))
% 51.51/51.72        | ((sk_C_1) = (k1_xboole_0))
% 51.51/51.72        | ((sk_B_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['1', '23'])).
% 51.51/51.72  thf('25', plain,
% 51.51/51.72      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf('26', plain,
% 51.51/51.72      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 51.51/51.72         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('split', [status(esa)], ['25'])).
% 51.51/51.72  thf('27', plain,
% 51.51/51.72      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('split', [status(esa)], ['25'])).
% 51.51/51.72  thf('28', plain,
% 51.51/51.72      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf('29', plain,
% 51.51/51.72      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 51.51/51.72       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('split', [status(esa)], ['28'])).
% 51.51/51.72  thf('30', plain,
% 51.51/51.72      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['4', '5'])).
% 51.51/51.72  thf('31', plain,
% 51.51/51.72      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf('32', plain,
% 51.51/51.72      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 51.51/51.72         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('split', [status(esa)], ['31'])).
% 51.51/51.72  thf('33', plain,
% 51.51/51.72      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 51.51/51.72         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('sup-', [status(thm)], ['30', '32'])).
% 51.51/51.72  thf('34', plain,
% 51.51/51.72      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('simplify', [status(thm)], ['33'])).
% 51.51/51.72  thf('35', plain,
% 51.51/51.72      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 51.51/51.72      inference('split', [status(esa)], ['25'])).
% 51.51/51.72  thf('36', plain,
% 51.51/51.72      ((((sk_B_1) != (sk_B_1)))
% 51.51/51.72         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 51.51/51.72             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('sup-', [status(thm)], ['34', '35'])).
% 51.51/51.72  thf('37', plain,
% 51.51/51.72      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['36'])).
% 51.51/51.72  thf('38', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('sat_resolution*', [status(thm)], ['27', '29', '37'])).
% 51.51/51.72  thf('39', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 51.51/51.72      inference('simpl_trail', [status(thm)], ['26', '38'])).
% 51.51/51.72  thf('40', plain, ((((sk_C_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('simplify_reflect-', [status(thm)], ['24', '39'])).
% 51.51/51.72  thf('41', plain,
% 51.51/51.72      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 51.51/51.72      inference('split', [status(esa)], ['31'])).
% 51.51/51.72  thf('42', plain,
% 51.51/51.72      (((((sk_C_1) != (sk_C_1)) | ((sk_B_1) = (k1_xboole_0))))
% 51.51/51.72         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 51.51/51.72      inference('sup-', [status(thm)], ['40', '41'])).
% 51.51/51.72  thf('43', plain,
% 51.51/51.72      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 51.51/51.72      inference('simplify', [status(thm)], ['42'])).
% 51.51/51.72  thf('44', plain,
% 51.51/51.72      (![X48 : $i, X49 : $i]:
% 51.51/51.72         ((r1_tarski @ X48 @ (k1_tarski @ X49)) | ((X48) != (k1_xboole_0)))),
% 51.51/51.72      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 51.51/51.72  thf('45', plain,
% 51.51/51.72      (![X49 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X49))),
% 51.51/51.72      inference('simplify', [status(thm)], ['44'])).
% 51.51/51.72  thf('46', plain,
% 51.51/51.72      (![X7 : $i, X8 : $i]:
% 51.51/51.72         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 51.51/51.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 51.51/51.72  thf('47', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['45', '46'])).
% 51.51/51.72  thf('48', plain,
% 51.51/51.72      (![X1 : $i, X3 : $i, X5 : $i]:
% 51.51/51.72         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 51.51/51.72          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 51.51/51.72          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 51.51/51.72          | (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 51.51/51.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 51.51/51.72  thf('49', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 51.51/51.72      inference('eq_fact', [status(thm)], ['48'])).
% 51.51/51.72  thf('50', plain,
% 51.51/51.72      (![X1 : $i, X3 : $i, X5 : $i]:
% 51.51/51.72         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 51.51/51.72          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X1)
% 51.51/51.72          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 51.51/51.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 51.51/51.72  thf('51', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 51.51/51.72          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['49', '50'])).
% 51.51/51.72  thf('52', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['51'])).
% 51.51/51.72  thf('53', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ X1 @ X0)))),
% 51.51/51.72      inference('eq_fact', [status(thm)], ['48'])).
% 51.51/51.72  thf('54', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 51.51/51.72      inference('clc', [status(thm)], ['52', '53'])).
% 51.51/51.72  thf('55', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 51.51/51.72      inference('clc', [status(thm)], ['52', '53'])).
% 51.51/51.72  thf('56', plain,
% 51.51/51.72      (![X11 : $i, X14 : $i]:
% 51.51/51.72         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['13'])).
% 51.51/51.72  thf('57', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 51.51/51.72          | ((sk_D @ X1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['55', '56'])).
% 51.51/51.72  thf('58', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 51.51/51.72      inference('clc', [status(thm)], ['52', '53'])).
% 51.51/51.72  thf('59', plain,
% 51.51/51.72      (![X1 : $i, X3 : $i, X5 : $i]:
% 51.51/51.72         (((X5) = (k2_xboole_0 @ X3 @ X1))
% 51.51/51.72          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X3)
% 51.51/51.72          | ~ (r2_hidden @ (sk_D @ X5 @ X1 @ X3) @ X5))),
% 51.51/51.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 51.51/51.72  thf('60', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 51.51/51.72          | ~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 51.51/51.72          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['58', '59'])).
% 51.51/51.72  thf('61', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (~ (r2_hidden @ (sk_D @ X1 @ X1 @ X0) @ X1)
% 51.51/51.72          | ((X1) = (k2_xboole_0 @ X0 @ X1)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['60'])).
% 51.51/51.72  thf('62', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (~ (r2_hidden @ X0 @ X1)
% 51.51/51.72          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 51.51/51.72          | ((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['57', '61'])).
% 51.51/51.72  thf('63', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 51.51/51.72          | ~ (r2_hidden @ X0 @ X1))),
% 51.51/51.72      inference('simplify', [status(thm)], ['62'])).
% 51.51/51.72  thf('64', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ X0 @ X1))
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ (k1_tarski @ (sk_D @ X1 @ X1 @ X0)) @ X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['54', '63'])).
% 51.51/51.72  thf('65', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['45', '46'])).
% 51.51/51.72  thf(t69_enumset1, axiom,
% 51.51/51.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 51.51/51.72  thf('66', plain,
% 51.51/51.72      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 51.51/51.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 51.51/51.72  thf('67', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['45', '46'])).
% 51.51/51.72  thf('68', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 51.51/51.72           = (k1_tarski @ X0))),
% 51.51/51.72      inference('sup+', [status(thm)], ['66', '67'])).
% 51.51/51.72  thf('69', plain,
% 51.51/51.72      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 51.51/51.72      inference('cnf', [status(esa)], [t7_xboole_0])).
% 51.51/51.72  thf('70', plain,
% 51.51/51.72      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 51.51/51.72         (~ (r2_hidden @ X4 @ X2)
% 51.51/51.72          | (r2_hidden @ X4 @ X3)
% 51.51/51.72          | (r2_hidden @ X4 @ X1)
% 51.51/51.72          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 51.51/51.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 51.51/51.72  thf('71', plain,
% 51.51/51.72      (![X1 : $i, X3 : $i, X4 : $i]:
% 51.51/51.72         ((r2_hidden @ X4 @ X1)
% 51.51/51.72          | (r2_hidden @ X4 @ X3)
% 51.51/51.72          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['70'])).
% 51.51/51.72  thf('72', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((k2_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 51.51/51.72          | (r2_hidden @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 51.51/51.72          | (r2_hidden @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['69', '71'])).
% 51.51/51.72  thf('73', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 51.51/51.72         (~ (r2_hidden @ X0 @ X3)
% 51.51/51.72          | (r2_hidden @ X0 @ X2)
% 51.51/51.72          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 51.51/51.72      inference('cnf', [status(esa)], [d3_xboole_0])).
% 51.51/51.72  thf('74', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X3 : $i]:
% 51.51/51.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 51.51/51.72      inference('simplify', [status(thm)], ['73'])).
% 51.51/51.72  thf('75', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.51/51.72         ((r2_hidden @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ X1)
% 51.51/51.72          | ((k2_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 51.51/51.72          | (r2_hidden @ (sk_B @ (k2_xboole_0 @ X1 @ X0)) @ 
% 51.51/51.72             (k2_xboole_0 @ X0 @ X2)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['72', '74'])).
% 51.51/51.72  thf('76', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         ((r2_hidden @ (sk_B @ (k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)) @ 
% 51.51/51.72           (k2_xboole_0 @ X1 @ X0))
% 51.51/51.72          | ((k2_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0)))),
% 51.51/51.72      inference('eq_fact', [status(thm)], ['75'])).
% 51.51/51.72  thf('77', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((r2_hidden @ 
% 51.51/51.72           (sk_B @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)) @ 
% 51.51/51.72           (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0)))
% 51.51/51.72          | ((k2_xboole_0 @ 
% 51.51/51.72              (k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0)) @ k1_xboole_0)
% 51.51/51.72              = (k1_xboole_0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['68', '76'])).
% 51.51/51.72  thf('78', plain,
% 51.51/51.72      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 51.51/51.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 51.51/51.72  thf('79', plain,
% 51.51/51.72      (![X49 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X49))),
% 51.51/51.72      inference('simplify', [status(thm)], ['44'])).
% 51.51/51.72  thf('80', plain,
% 51.51/51.72      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X0 @ X0))),
% 51.51/51.72      inference('sup+', [status(thm)], ['78', '79'])).
% 51.51/51.72  thf('81', plain,
% 51.51/51.72      (![X7 : $i, X8 : $i]:
% 51.51/51.72         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 51.51/51.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 51.51/51.72  thf('82', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 51.51/51.72           = (k2_tarski @ X0 @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['80', '81'])).
% 51.51/51.72  thf('83', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((k2_xboole_0 @ k1_xboole_0 @ (k2_tarski @ X0 @ X0))
% 51.51/51.72           = (k2_tarski @ X0 @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['80', '81'])).
% 51.51/51.72  thf('84', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((r2_hidden @ 
% 51.51/51.72           (sk_B @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)) @ 
% 51.51/51.72           (k2_tarski @ X0 @ X0))
% 51.51/51.72          | ((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0)
% 51.51/51.72              = (k1_xboole_0)))),
% 51.51/51.72      inference('demod', [status(thm)], ['77', '82', '83'])).
% 51.51/51.72  thf('85', plain,
% 51.51/51.72      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 51.51/51.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 51.51/51.72  thf('86', plain,
% 51.51/51.72      (![X11 : $i, X14 : $i]:
% 51.51/51.72         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['13'])).
% 51.51/51.72  thf('87', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['85', '86'])).
% 51.51/51.72  thf('88', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         (((k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 51.51/51.72          | ((sk_B @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)) = (X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['84', '87'])).
% 51.51/51.72  thf('89', plain,
% 51.51/51.72      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 51.51/51.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 51.51/51.72  thf('90', plain,
% 51.51/51.72      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 51.51/51.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 51.51/51.72  thf('91', plain,
% 51.51/51.72      (![X44 : $i, X45 : $i]:
% 51.51/51.72         ((r2_hidden @ X44 @ X45) | ~ (r1_tarski @ (k1_tarski @ X44) @ X45))),
% 51.51/51.72      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 51.51/51.72  thf('92', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 51.51/51.72      inference('sup-', [status(thm)], ['90', '91'])).
% 51.51/51.72  thf('93', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X3 : $i]:
% 51.51/51.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 51.51/51.72      inference('simplify', [status(thm)], ['73'])).
% 51.51/51.72  thf('94', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.51/51.72         (r2_hidden @ X1 @ 
% 51.51/51.72          (k2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X2))),
% 51.51/51.72      inference('sup-', [status(thm)], ['92', '93'])).
% 51.51/51.72  thf('95', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 51.51/51.72         (r2_hidden @ X0 @ 
% 51.51/51.72          (k2_xboole_0 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X2) @ X1))),
% 51.51/51.72      inference('sup+', [status(thm)], ['89', '94'])).
% 51.51/51.72  thf('96', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         ((r2_hidden @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 51.51/51.72          | ((sk_B @ (k2_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)) = (X1)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['88', '95'])).
% 51.51/51.72  thf('97', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 51.51/51.72          | ((sk_B @ (k2_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)) = (X1)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['65', '96'])).
% 51.51/51.72  thf('98', plain,
% 51.51/51.72      (![X11 : $i, X14 : $i]:
% 51.51/51.72         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['13'])).
% 51.51/51.72  thf('99', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((sk_B @ (k2_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0)) = (X1))
% 51.51/51.72          | ((X1) = (X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['97', '98'])).
% 51.51/51.72  thf('100', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((sk_B @ (k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)) = (X0))),
% 51.51/51.72      inference('condensation', [status(thm)], ['99'])).
% 51.51/51.72  thf('101', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         (((sk_B @ k1_xboole_0) = (sk_D @ X0 @ X0 @ k1_xboole_0))
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['64', '100'])).
% 51.51/51.72  thf('102', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X0) = (k2_xboole_0 @ X1 @ X0))
% 51.51/51.72          | (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 51.51/51.72      inference('clc', [status(thm)], ['52', '53'])).
% 51.51/51.72  thf('103', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         ((r2_hidden @ (sk_B @ k1_xboole_0) @ k1_xboole_0)
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['101', '102'])).
% 51.51/51.72  thf('104', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         (((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))
% 51.51/51.72          | (r2_hidden @ (sk_B @ k1_xboole_0) @ k1_xboole_0))),
% 51.51/51.72      inference('simplify', [status(thm)], ['103'])).
% 51.51/51.72  thf('105', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i, X3 : $i]:
% 51.51/51.72         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 51.51/51.72      inference('simplify', [status(thm)], ['73'])).
% 51.51/51.72  thf('106', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 51.51/51.72          | (r2_hidden @ (sk_B @ k1_xboole_0) @ 
% 51.51/51.72             (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['104', '105'])).
% 51.51/51.72  thf('107', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         ((r2_hidden @ (sk_B @ k1_xboole_0) @ (k1_tarski @ X0))
% 51.51/51.72          | ((X1) = (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 51.51/51.72      inference('sup+', [status(thm)], ['47', '106'])).
% 51.51/51.72  thf('108', plain,
% 51.51/51.72      (![X11 : $i, X14 : $i]:
% 51.51/51.72         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 51.51/51.72      inference('simplify', [status(thm)], ['13'])).
% 51.51/51.72  thf('109', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 51.51/51.72          | ((sk_B @ k1_xboole_0) = (X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['107', '108'])).
% 51.51/51.72  thf('110', plain,
% 51.51/51.72      (![X0 : $i]:
% 51.51/51.72         (((sk_B @ k1_xboole_0) != (k2_xboole_0 @ k1_xboole_0 @ X0))
% 51.51/51.72          | ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 51.51/51.72      inference('eq_fact', [status(thm)], ['109'])).
% 51.51/51.72  thf('111', plain,
% 51.51/51.72      (![X0 : $i, X1 : $i]:
% 51.51/51.72         (((X1) = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 51.51/51.72          | ((sk_B @ k1_xboole_0) = (X0)))),
% 51.51/51.72      inference('sup-', [status(thm)], ['107', '108'])).
% 51.51/51.72  thf('112', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 51.51/51.72      inference('clc', [status(thm)], ['110', '111'])).
% 51.51/51.72  thf('113', plain,
% 51.51/51.72      ((![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B_1 @ X0)))
% 51.51/51.72         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 51.51/51.72      inference('sup+', [status(thm)], ['43', '112'])).
% 51.51/51.72  thf('114', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 51.51/51.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 51.51/51.72  thf('115', plain,
% 51.51/51.72      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('simplify', [status(thm)], ['33'])).
% 51.51/51.72  thf('116', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 51.51/51.72      inference('clc', [status(thm)], ['110', '111'])).
% 51.51/51.72  thf('117', plain,
% 51.51/51.72      ((![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B_1 @ X0)))
% 51.51/51.72         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('sup+', [status(thm)], ['115', '116'])).
% 51.51/51.72  thf('118', plain,
% 51.51/51.72      ((((sk_C_1) = (k1_tarski @ sk_A)))
% 51.51/51.72         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 51.51/51.72      inference('sup+', [status(thm)], ['114', '117'])).
% 51.51/51.72  thf('119', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 51.51/51.72      inference('simpl_trail', [status(thm)], ['26', '38'])).
% 51.51/51.72  thf('120', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 51.51/51.72  thf('121', plain,
% 51.51/51.72      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 51.51/51.72      inference('split', [status(esa)], ['31'])).
% 51.51/51.72  thf('122', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 51.51/51.72      inference('sat_resolution*', [status(thm)], ['120', '121'])).
% 51.51/51.72  thf('123', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ sk_B_1 @ X0))),
% 51.51/51.72      inference('simpl_trail', [status(thm)], ['113', '122'])).
% 51.51/51.72  thf('124', plain, (((k1_tarski @ sk_A) = (sk_C_1))),
% 51.51/51.72      inference('demod', [status(thm)], ['0', '123'])).
% 51.51/51.72  thf('125', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 51.51/51.72      inference('simpl_trail', [status(thm)], ['26', '38'])).
% 51.51/51.72  thf('126', plain, ($false),
% 51.51/51.72      inference('simplify_reflect-', [status(thm)], ['124', '125'])).
% 51.51/51.72  
% 51.51/51.72  % SZS output end Refutation
% 51.51/51.72  
% 51.51/51.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
