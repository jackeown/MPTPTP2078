%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iNWh9q0Q1T

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:43 EST 2020

% Result     : Theorem 9.33s
% Output     : Refutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 409 expanded)
%              Number of leaves         :   37 ( 123 expanded)
%              Depth                    :   24
%              Number of atoms          :  786 (3057 expanded)
%              Number of equality atoms :   50 ( 253 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t13_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
      <=> ( ( r2_hidden @ A @ B )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_ordinal1])).

thf('0',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A = sk_B )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( sk_A != sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('8',plain,(
    ! [X44: $i] :
      ( r2_hidden @ X44 @ ( k1_ordinal1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('9',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['7','12'])).

thf('14',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('15',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('18',plain,(
    ! [X43: $i] :
      ( ( k1_ordinal1 @ X43 )
      = ( k2_xboole_0 @ X43 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','23'])).

thf('25',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['24'])).

thf('26',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k1_enumset1 @ X23 @ X23 @ X24 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X43: $i] :
      ( ( k1_ordinal1 @ X43 )
      = ( k2_xboole_0 @ X43 @ ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( zip_tseitin_0 @ X13 @ X12 @ X11 )
      | ( zip_tseitin_1 @ X13 @ X12 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( zip_tseitin_1 @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X0 )
      | ( zip_tseitin_0 @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k1_enumset1 @ sk_B @ sk_B @ sk_B ) )
    | ( zip_tseitin_0 @ sk_A @ ( k1_enumset1 @ sk_B @ sk_B @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k1_enumset1 @ sk_B @ sk_B @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('38',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_B ) )
    | ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['34','35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('43',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('44',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X36 @ X37 )
      | ( r2_hidden @ X38 @ X37 )
      | ( X37
        = ( k4_xboole_0 @ X37 @ ( k2_tarski @ X36 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('47',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('51',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ~ ( r1_tarski @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','53'])).

thf('55',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( zip_tseitin_1 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['38','54'])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( zip_tseitin_1 @ X8 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('57',plain,
    ( ( zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('59',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('60',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['24','59'])).

thf('61',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['58','60'])).

thf('62',plain,(
    zip_tseitin_0 @ sk_A @ ( k1_tarski @ sk_B ) @ sk_B ),
    inference(clc,[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('64',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('65',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_tarski @ X32 @ ( k3_tarski @ X33 ) )
      | ~ ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('66',plain,(
    r1_tarski @ sk_A @ ( k3_tarski @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X22: $i] :
      ( ( k2_tarski @ X22 @ X22 )
      = ( k1_tarski @ X22 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('68',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X34 @ X35 ) )
      = ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('70',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X14: $i,X16: $i] :
      ( ( X14 = X16 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['6','13'])).

thf('76',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('78',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('79',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ~ ( r1_tarski @ X40 @ X42 )
      | ( r1_tarski @ ( k1_setfam_1 @ X41 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ sk_B ) ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('81',plain,(
    ! [X39: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X39 ) )
      = X39 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['76','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.iNWh9q0Q1T
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 9.33/9.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.33/9.65  % Solved by: fo/fo7.sh
% 9.33/9.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.33/9.65  % done 5648 iterations in 9.183s
% 9.33/9.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.33/9.65  % SZS output start Refutation
% 9.33/9.65  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 9.33/9.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 9.33/9.65  thf(sk_A_type, type, sk_A: $i).
% 9.33/9.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.33/9.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 9.33/9.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 9.33/9.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 9.33/9.65  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 9.33/9.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 9.33/9.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.33/9.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 9.33/9.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 9.33/9.65  thf(sk_B_type, type, sk_B: $i).
% 9.33/9.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 9.33/9.65  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 9.33/9.65  thf(t13_ordinal1, conjecture,
% 9.33/9.65    (![A:$i,B:$i]:
% 9.33/9.65     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 9.33/9.65       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 9.33/9.65  thf(zf_stmt_0, negated_conjecture,
% 9.33/9.65    (~( ![A:$i,B:$i]:
% 9.33/9.65        ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 9.33/9.65          ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ) )),
% 9.33/9.65    inference('cnf.neg', [status(esa)], [t13_ordinal1])).
% 9.33/9.65  thf('0', plain,
% 9.33/9.65      ((((sk_A) = (sk_B))
% 9.33/9.65        | (r2_hidden @ sk_A @ sk_B)
% 9.33/9.65        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.33/9.65  thf('1', plain,
% 9.33/9.65      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 9.33/9.65         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 9.33/9.65      inference('split', [status(esa)], ['0'])).
% 9.33/9.65  thf('2', plain,
% 9.33/9.65      ((~ (r2_hidden @ sk_A @ sk_B)
% 9.33/9.65        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.33/9.65  thf('3', plain,
% 9.33/9.65      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 9.33/9.65         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 9.33/9.65      inference('split', [status(esa)], ['2'])).
% 9.33/9.65  thf('4', plain,
% 9.33/9.65      ((((sk_A) = (sk_B))
% 9.33/9.65        | (r2_hidden @ sk_A @ sk_B)
% 9.33/9.65        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.33/9.65  thf('5', plain,
% 9.33/9.65      ((((sk_A) != (sk_B)) | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.33/9.65  thf('6', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 9.33/9.65      inference('split', [status(esa)], ['5'])).
% 9.33/9.65  thf('7', plain,
% 9.33/9.65      (~ (((sk_A) = (sk_B))) | ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('split', [status(esa)], ['5'])).
% 9.33/9.65  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 9.33/9.65  thf('8', plain, (![X44 : $i]: (r2_hidden @ X44 @ (k1_ordinal1 @ X44))),
% 9.33/9.65      inference('cnf', [status(esa)], [t10_ordinal1])).
% 9.33/9.65  thf('9', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 9.33/9.65      inference('split', [status(esa)], ['0'])).
% 9.33/9.65  thf('10', plain,
% 9.33/9.65      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 9.33/9.65         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 9.33/9.65      inference('split', [status(esa)], ['2'])).
% 9.33/9.65  thf('11', plain,
% 9.33/9.65      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 9.33/9.65         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 9.33/9.65             (((sk_A) = (sk_B))))),
% 9.33/9.65      inference('sup-', [status(thm)], ['9', '10'])).
% 9.33/9.65  thf('12', plain,
% 9.33/9.65      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | ~ (((sk_A) = (sk_B)))),
% 9.33/9.65      inference('sup-', [status(thm)], ['8', '11'])).
% 9.33/9.65  thf('13', plain, (~ (((sk_A) = (sk_B)))),
% 9.33/9.65      inference('sat_resolution*', [status(thm)], ['7', '12'])).
% 9.33/9.65  thf('14', plain, (((sk_A) != (sk_B))),
% 9.33/9.65      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 9.33/9.65  thf('15', plain,
% 9.33/9.65      (((r2_hidden @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('simplify_reflect-', [status(thm)], ['4', '14'])).
% 9.33/9.65  thf('16', plain,
% 9.33/9.65      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 9.33/9.65         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 9.33/9.65      inference('split', [status(esa)], ['2'])).
% 9.33/9.65  thf('17', plain,
% 9.33/9.65      (((r2_hidden @ sk_A @ sk_B))
% 9.33/9.65         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 9.33/9.65      inference('sup-', [status(thm)], ['15', '16'])).
% 9.33/9.65  thf(d1_ordinal1, axiom,
% 9.33/9.65    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 9.33/9.65  thf('18', plain,
% 9.33/9.65      (![X43 : $i]:
% 9.33/9.65         ((k1_ordinal1 @ X43) = (k2_xboole_0 @ X43 @ (k1_tarski @ X43)))),
% 9.33/9.65      inference('cnf', [status(esa)], [d1_ordinal1])).
% 9.33/9.65  thf(t7_xboole_1, axiom,
% 9.33/9.65    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 9.33/9.65  thf('19', plain,
% 9.33/9.65      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 9.33/9.65      inference('cnf', [status(esa)], [t7_xboole_1])).
% 9.33/9.65  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ (k1_ordinal1 @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['18', '19'])).
% 9.33/9.65  thf(d3_tarski, axiom,
% 9.33/9.65    (![A:$i,B:$i]:
% 9.33/9.65     ( ( r1_tarski @ A @ B ) <=>
% 9.33/9.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 9.33/9.65  thf('21', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.33/9.65         (~ (r2_hidden @ X0 @ X1)
% 9.33/9.65          | (r2_hidden @ X0 @ X2)
% 9.33/9.65          | ~ (r1_tarski @ X1 @ X2))),
% 9.33/9.65      inference('cnf', [status(esa)], [d3_tarski])).
% 9.33/9.65  thf('22', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 9.33/9.65      inference('sup-', [status(thm)], ['20', '21'])).
% 9.33/9.65  thf('23', plain,
% 9.33/9.65      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 9.33/9.65         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 9.33/9.65      inference('sup-', [status(thm)], ['17', '22'])).
% 9.33/9.65  thf('24', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('demod', [status(thm)], ['3', '23'])).
% 9.33/9.65  thf('25', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('sat_resolution*', [status(thm)], ['24'])).
% 9.33/9.65  thf('26', plain, ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))),
% 9.33/9.65      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 9.33/9.65  thf(t70_enumset1, axiom,
% 9.33/9.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 9.33/9.65  thf('27', plain,
% 9.33/9.65      (![X23 : $i, X24 : $i]:
% 9.33/9.65         ((k1_enumset1 @ X23 @ X23 @ X24) = (k2_tarski @ X23 @ X24))),
% 9.33/9.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 9.33/9.65  thf(t69_enumset1, axiom,
% 9.33/9.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 9.33/9.65  thf('28', plain,
% 9.33/9.65      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 9.33/9.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 9.33/9.65  thf('29', plain,
% 9.33/9.65      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['27', '28'])).
% 9.33/9.65  thf('30', plain,
% 9.33/9.65      (![X43 : $i]:
% 9.33/9.65         ((k1_ordinal1 @ X43) = (k2_xboole_0 @ X43 @ (k1_tarski @ X43)))),
% 9.33/9.65      inference('cnf', [status(esa)], [d1_ordinal1])).
% 9.33/9.65  thf('31', plain,
% 9.33/9.65      (![X0 : $i]:
% 9.33/9.65         ((k1_ordinal1 @ X0)
% 9.33/9.65           = (k2_xboole_0 @ X0 @ (k1_enumset1 @ X0 @ X0 @ X0)))),
% 9.33/9.65      inference('sup+', [status(thm)], ['29', '30'])).
% 9.33/9.65  thf(t5_xboole_0, axiom,
% 9.33/9.65    (![A:$i,B:$i,C:$i]:
% 9.33/9.65     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 9.33/9.65          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 9.33/9.65          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 9.33/9.65  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 9.33/9.65  thf(zf_stmt_2, axiom,
% 9.33/9.65    (![C:$i,B:$i,A:$i]:
% 9.33/9.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 9.33/9.65       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 9.33/9.65  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 9.33/9.65  thf(zf_stmt_4, axiom,
% 9.33/9.65    (![C:$i,B:$i,A:$i]:
% 9.33/9.65     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 9.33/9.65       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 9.33/9.65  thf(zf_stmt_5, axiom,
% 9.33/9.65    (![A:$i,B:$i,C:$i]:
% 9.33/9.65     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 9.33/9.65          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 9.33/9.65          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 9.33/9.65          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 9.33/9.65  thf('32', plain,
% 9.33/9.65      (![X11 : $i, X12 : $i, X13 : $i]:
% 9.33/9.65         (~ (r1_xboole_0 @ X11 @ X12)
% 9.33/9.65          | (zip_tseitin_0 @ X13 @ X12 @ X11)
% 9.33/9.65          | (zip_tseitin_1 @ X13 @ X12 @ X11)
% 9.33/9.65          | ~ (r2_hidden @ X13 @ (k2_xboole_0 @ X11 @ X12)))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 9.33/9.65  thf('33', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 9.33/9.65          | (zip_tseitin_1 @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X0)
% 9.33/9.65          | (zip_tseitin_0 @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0) @ X0)
% 9.33/9.65          | ~ (r1_xboole_0 @ X0 @ (k1_enumset1 @ X0 @ X0 @ X0)))),
% 9.33/9.65      inference('sup-', [status(thm)], ['31', '32'])).
% 9.33/9.65  thf('34', plain,
% 9.33/9.65      ((~ (r1_xboole_0 @ sk_B @ (k1_enumset1 @ sk_B @ sk_B @ sk_B))
% 9.33/9.65        | (zip_tseitin_0 @ sk_A @ (k1_enumset1 @ sk_B @ sk_B @ sk_B) @ sk_B)
% 9.33/9.65        | (zip_tseitin_1 @ sk_A @ (k1_enumset1 @ sk_B @ sk_B @ sk_B) @ sk_B))),
% 9.33/9.65      inference('sup-', [status(thm)], ['26', '33'])).
% 9.33/9.65  thf('35', plain,
% 9.33/9.65      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['27', '28'])).
% 9.33/9.65  thf('36', plain,
% 9.33/9.65      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['27', '28'])).
% 9.33/9.65  thf('37', plain,
% 9.33/9.65      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['27', '28'])).
% 9.33/9.65  thf('38', plain,
% 9.33/9.65      ((~ (r1_xboole_0 @ sk_B @ (k1_tarski @ sk_B))
% 9.33/9.65        | (zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 9.33/9.65        | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B))),
% 9.33/9.65      inference('demod', [status(thm)], ['34', '35', '36', '37'])).
% 9.33/9.65  thf('39', plain,
% 9.33/9.65      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['27', '28'])).
% 9.33/9.65  thf(d10_xboole_0, axiom,
% 9.33/9.65    (![A:$i,B:$i]:
% 9.33/9.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.33/9.65  thf('40', plain,
% 9.33/9.65      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 9.33/9.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.33/9.65  thf('41', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 9.33/9.65      inference('simplify', [status(thm)], ['40'])).
% 9.33/9.65  thf('42', plain,
% 9.33/9.65      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['27', '28'])).
% 9.33/9.65  thf('43', plain,
% 9.33/9.65      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 9.33/9.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 9.33/9.65  thf(t144_zfmisc_1, axiom,
% 9.33/9.65    (![A:$i,B:$i,C:$i]:
% 9.33/9.65     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 9.33/9.65          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 9.33/9.65  thf('44', plain,
% 9.33/9.65      (![X36 : $i, X37 : $i, X38 : $i]:
% 9.33/9.65         ((r2_hidden @ X36 @ X37)
% 9.33/9.65          | (r2_hidden @ X38 @ X37)
% 9.33/9.65          | ((X37) = (k4_xboole_0 @ X37 @ (k2_tarski @ X36 @ X38))))),
% 9.33/9.65      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 9.33/9.65  thf('45', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         (((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 9.33/9.65          | (r2_hidden @ X0 @ X1)
% 9.33/9.65          | (r2_hidden @ X0 @ X1))),
% 9.33/9.65      inference('sup+', [status(thm)], ['43', '44'])).
% 9.33/9.65  thf('46', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         ((r2_hidden @ X0 @ X1)
% 9.33/9.65          | ((X1) = (k4_xboole_0 @ X1 @ (k1_tarski @ X0))))),
% 9.33/9.65      inference('simplify', [status(thm)], ['45'])).
% 9.33/9.65  thf(t83_xboole_1, axiom,
% 9.33/9.65    (![A:$i,B:$i]:
% 9.33/9.65     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 9.33/9.65  thf('47', plain,
% 9.33/9.65      (![X19 : $i, X21 : $i]:
% 9.33/9.65         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 9.33/9.65      inference('cnf', [status(esa)], [t83_xboole_1])).
% 9.33/9.65  thf('48', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         (((X0) != (X0))
% 9.33/9.65          | (r2_hidden @ X1 @ X0)
% 9.33/9.65          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 9.33/9.65      inference('sup-', [status(thm)], ['46', '47'])).
% 9.33/9.65  thf('49', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 9.33/9.65      inference('simplify', [status(thm)], ['48'])).
% 9.33/9.65  thf('50', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         ((r1_xboole_0 @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0))
% 9.33/9.65          | (r2_hidden @ X0 @ X1))),
% 9.33/9.65      inference('sup+', [status(thm)], ['42', '49'])).
% 9.33/9.65  thf(t7_ordinal1, axiom,
% 9.33/9.65    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.33/9.65  thf('51', plain,
% 9.33/9.65      (![X45 : $i, X46 : $i]:
% 9.33/9.65         (~ (r2_hidden @ X45 @ X46) | ~ (r1_tarski @ X46 @ X45))),
% 9.33/9.65      inference('cnf', [status(esa)], [t7_ordinal1])).
% 9.33/9.65  thf('52', plain,
% 9.33/9.65      (![X0 : $i, X1 : $i]:
% 9.33/9.65         ((r1_xboole_0 @ X0 @ (k1_enumset1 @ X1 @ X1 @ X1))
% 9.33/9.65          | ~ (r1_tarski @ X0 @ X1))),
% 9.33/9.65      inference('sup-', [status(thm)], ['50', '51'])).
% 9.33/9.65  thf('53', plain,
% 9.33/9.65      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_enumset1 @ X0 @ X0 @ X0))),
% 9.33/9.65      inference('sup-', [status(thm)], ['41', '52'])).
% 9.33/9.65  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k1_tarski @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['39', '53'])).
% 9.33/9.65  thf('55', plain,
% 9.33/9.65      (((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 9.33/9.65        | (zip_tseitin_1 @ sk_A @ (k1_tarski @ sk_B) @ sk_B))),
% 9.33/9.65      inference('demod', [status(thm)], ['38', '54'])).
% 9.33/9.65  thf('56', plain,
% 9.33/9.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 9.33/9.65         ((r2_hidden @ X8 @ X9) | ~ (zip_tseitin_1 @ X8 @ X10 @ X9))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 9.33/9.65  thf('57', plain,
% 9.33/9.65      (((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)
% 9.33/9.65        | (r2_hidden @ sk_A @ sk_B))),
% 9.33/9.65      inference('sup-', [status(thm)], ['55', '56'])).
% 9.33/9.65  thf('58', plain,
% 9.33/9.65      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 9.33/9.65      inference('split', [status(esa)], ['2'])).
% 9.33/9.65  thf('59', plain,
% 9.33/9.65      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 9.33/9.65       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 9.33/9.65      inference('split', [status(esa)], ['2'])).
% 9.33/9.65  thf('60', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 9.33/9.65      inference('sat_resolution*', [status(thm)], ['24', '59'])).
% 9.33/9.65  thf('61', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 9.33/9.65      inference('simpl_trail', [status(thm)], ['58', '60'])).
% 9.33/9.65  thf('62', plain, ((zip_tseitin_0 @ sk_A @ (k1_tarski @ sk_B) @ sk_B)),
% 9.33/9.65      inference('clc', [status(thm)], ['57', '61'])).
% 9.33/9.65  thf('63', plain,
% 9.33/9.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 9.33/9.65         ((r2_hidden @ X5 @ X6) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7))),
% 9.33/9.65      inference('cnf', [status(esa)], [zf_stmt_4])).
% 9.33/9.65  thf('64', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 9.33/9.65      inference('sup-', [status(thm)], ['62', '63'])).
% 9.33/9.65  thf(l49_zfmisc_1, axiom,
% 9.33/9.65    (![A:$i,B:$i]:
% 9.33/9.65     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 9.33/9.65  thf('65', plain,
% 9.33/9.65      (![X32 : $i, X33 : $i]:
% 9.33/9.65         ((r1_tarski @ X32 @ (k3_tarski @ X33)) | ~ (r2_hidden @ X32 @ X33))),
% 9.33/9.65      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 9.33/9.65  thf('66', plain, ((r1_tarski @ sk_A @ (k3_tarski @ (k1_tarski @ sk_B)))),
% 9.33/9.65      inference('sup-', [status(thm)], ['64', '65'])).
% 9.33/9.65  thf('67', plain,
% 9.33/9.65      (![X22 : $i]: ((k2_tarski @ X22 @ X22) = (k1_tarski @ X22))),
% 9.33/9.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 9.33/9.65  thf(l51_zfmisc_1, axiom,
% 9.33/9.65    (![A:$i,B:$i]:
% 9.33/9.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 9.33/9.65  thf('68', plain,
% 9.33/9.65      (![X34 : $i, X35 : $i]:
% 9.33/9.65         ((k3_tarski @ (k2_tarski @ X34 @ X35)) = (k2_xboole_0 @ X34 @ X35))),
% 9.33/9.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 9.33/9.65  thf('69', plain,
% 9.33/9.65      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 9.33/9.65      inference('sup+', [status(thm)], ['67', '68'])).
% 9.33/9.65  thf(idempotence_k2_xboole_0, axiom,
% 9.33/9.65    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 9.33/9.65  thf('70', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ X4) = (X4))),
% 9.33/9.65      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 9.33/9.65  thf('71', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 9.33/9.65      inference('demod', [status(thm)], ['69', '70'])).
% 9.33/9.65  thf('72', plain, ((r1_tarski @ sk_A @ sk_B)),
% 9.33/9.65      inference('demod', [status(thm)], ['66', '71'])).
% 9.33/9.65  thf('73', plain,
% 9.33/9.65      (![X14 : $i, X16 : $i]:
% 9.33/9.65         (((X14) = (X16))
% 9.33/9.65          | ~ (r1_tarski @ X16 @ X14)
% 9.33/9.65          | ~ (r1_tarski @ X14 @ X16))),
% 9.33/9.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.33/9.65  thf('74', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 9.33/9.65      inference('sup-', [status(thm)], ['72', '73'])).
% 9.33/9.65  thf('75', plain, (((sk_A) != (sk_B))),
% 9.33/9.65      inference('simpl_trail', [status(thm)], ['6', '13'])).
% 9.33/9.65  thf('76', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 9.33/9.65      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 9.33/9.65  thf('77', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 9.33/9.65      inference('simplify', [status(thm)], ['40'])).
% 9.33/9.65  thf('78', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 9.33/9.65      inference('sup-', [status(thm)], ['62', '63'])).
% 9.33/9.65  thf(t8_setfam_1, axiom,
% 9.33/9.65    (![A:$i,B:$i,C:$i]:
% 9.33/9.65     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 9.33/9.65       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 9.33/9.65  thf('79', plain,
% 9.33/9.65      (![X40 : $i, X41 : $i, X42 : $i]:
% 9.33/9.65         (~ (r2_hidden @ X40 @ X41)
% 9.33/9.65          | ~ (r1_tarski @ X40 @ X42)
% 9.33/9.65          | (r1_tarski @ (k1_setfam_1 @ X41) @ X42))),
% 9.33/9.65      inference('cnf', [status(esa)], [t8_setfam_1])).
% 9.33/9.65  thf('80', plain,
% 9.33/9.65      (![X0 : $i]:
% 9.33/9.65         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ sk_B)) @ X0)
% 9.33/9.65          | ~ (r1_tarski @ sk_A @ X0))),
% 9.33/9.65      inference('sup-', [status(thm)], ['78', '79'])).
% 9.33/9.65  thf(t11_setfam_1, axiom,
% 9.33/9.65    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 9.33/9.65  thf('81', plain, (![X39 : $i]: ((k1_setfam_1 @ (k1_tarski @ X39)) = (X39))),
% 9.33/9.65      inference('cnf', [status(esa)], [t11_setfam_1])).
% 9.33/9.65  thf('82', plain,
% 9.33/9.65      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 9.33/9.65      inference('demod', [status(thm)], ['80', '81'])).
% 9.33/9.65  thf('83', plain, ((r1_tarski @ sk_B @ sk_A)),
% 9.33/9.65      inference('sup-', [status(thm)], ['77', '82'])).
% 9.33/9.65  thf('84', plain, ($false), inference('demod', [status(thm)], ['76', '83'])).
% 9.33/9.65  
% 9.33/9.65  % SZS output end Refutation
% 9.33/9.65  
% 9.33/9.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
