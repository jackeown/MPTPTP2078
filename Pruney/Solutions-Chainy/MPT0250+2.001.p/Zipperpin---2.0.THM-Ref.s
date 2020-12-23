%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kc13SHpQ0l

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:47 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 262 expanded)
%              Number of leaves         :   28 (  95 expanded)
%              Depth                    :   15
%              Number of atoms          :  706 (2275 expanded)
%              Number of equality atoms :   62 ( 227 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
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
    inference(cnf,[status(esa)],[zf_stmt_3])).

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
      ( ( X6 != X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k3_tarski @ X39 ) )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t43_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ) )).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( k2_enumset1 @ X17 @ X18 @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k2_tarski @ X17 @ X18 ) @ ( k2_tarski @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_enumset1 @ X2 @ X1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t125_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ C @ B @ A ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X24 @ X23 @ X22 @ X21 )
      = ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t125_enumset1])).

thf('23',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X31 @ X31 @ X32 @ X33 )
      = ( k1_enumset1 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k1_enumset1 @ X1 @ X0 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t43_enumset1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X40 @ X41 ) )
      = ( k2_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','38'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r2_xboole_0 @ X2 @ X4 )
      | ( X2 = X4 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('44',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
    | ( r2_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(antisymmetry_r2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
     => ~ ( r2_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_xboole_0])).

thf('46',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
    | ~ ( r2_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('49',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B )
    | ~ ( r2_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('53',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('54',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k3_tarski @ X39 ) )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('61',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ ( k2_tarski @ X42 @ X44 ) @ X43 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['51','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kc13SHpQ0l
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:33:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.83/1.02  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.02  % Solved by: fo/fo7.sh
% 0.83/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.02  % done 1465 iterations in 0.570s
% 0.83/1.02  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.02  % SZS output start Refutation
% 0.83/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.02  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.02  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.02  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.83/1.02  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.83/1.02  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.83/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.02  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.83/1.02  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.83/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.02  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.02  thf(t45_zfmisc_1, conjecture,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.83/1.02       ( r2_hidden @ A @ B ) ))).
% 0.83/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.02    (~( ![A:$i,B:$i]:
% 0.83/1.02        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.83/1.02          ( r2_hidden @ A @ B ) ) )),
% 0.83/1.02    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.83/1.02  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf(t70_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.83/1.02  thf('1', plain,
% 0.83/1.02      (![X29 : $i, X30 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.83/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.83/1.02  thf(d1_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.83/1.02       ( ![E:$i]:
% 0.83/1.02         ( ( r2_hidden @ E @ D ) <=>
% 0.83/1.02           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.83/1.02  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.83/1.02  thf(zf_stmt_2, axiom,
% 0.83/1.02    (![E:$i,C:$i,B:$i,A:$i]:
% 0.83/1.02     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.83/1.02       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.83/1.02  thf(zf_stmt_3, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.83/1.02       ( ![E:$i]:
% 0.83/1.02         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.83/1.02  thf('2', plain,
% 0.83/1.02      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.83/1.02         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.83/1.02          | (r2_hidden @ X10 @ X14)
% 0.83/1.02          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.83/1.02  thf('3', plain,
% 0.83/1.02      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.83/1.02         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.83/1.02          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.83/1.02      inference('simplify', [status(thm)], ['2'])).
% 0.83/1.02  thf('4', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.83/1.02          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['1', '3'])).
% 0.83/1.02  thf('5', plain,
% 0.83/1.02      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.02         (((X6) != (X7)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.83/1.02  thf('6', plain,
% 0.83/1.02      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X7 @ X7 @ X8 @ X5)),
% 0.83/1.02      inference('simplify', [status(thm)], ['5'])).
% 0.83/1.02  thf('7', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.83/1.02      inference('sup-', [status(thm)], ['4', '6'])).
% 0.83/1.02  thf(l49_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.83/1.02  thf('8', plain,
% 0.83/1.02      (![X38 : $i, X39 : $i]:
% 0.83/1.02         ((r1_tarski @ X38 @ (k3_tarski @ X39)) | ~ (r2_hidden @ X38 @ X39))),
% 0.83/1.02      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.83/1.02  thf('9', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['7', '8'])).
% 0.83/1.02  thf(t71_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.83/1.02  thf('10', plain,
% 0.83/1.02      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.83/1.02           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.83/1.02      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.83/1.02  thf(t69_enumset1, axiom,
% 0.83/1.02    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.83/1.02  thf('11', plain,
% 0.83/1.02      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.83/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.02  thf(t43_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.83/1.02       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) ))).
% 0.83/1.02  thf('12', plain,
% 0.83/1.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.83/1.02           = (k2_xboole_0 @ (k2_tarski @ X25 @ X26) @ (k1_tarski @ X27)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.83/1.02  thf('13', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.83/1.02           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k2_tarski @ X0 @ X0)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['11', '12'])).
% 0.83/1.02  thf(l53_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.83/1.02       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.83/1.02  thf('14', plain,
% 0.83/1.02      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X17 @ X18 @ X19 @ X20)
% 0.83/1.02           = (k2_xboole_0 @ (k2_tarski @ X17 @ X18) @ (k2_tarski @ X19 @ X20)))),
% 0.83/1.02      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.83/1.02  thf('15', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 0.83/1.02      inference('demod', [status(thm)], ['13', '14'])).
% 0.83/1.02  thf('16', plain,
% 0.83/1.02      (![X29 : $i, X30 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.83/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.83/1.02  thf(l51_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.83/1.02  thf('17', plain,
% 0.83/1.02      (![X40 : $i, X41 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 0.83/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.02  thf('18', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['16', '17'])).
% 0.83/1.02  thf('19', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X0 @ X0))
% 0.83/1.02           = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['15', '18'])).
% 0.83/1.02  thf('20', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['10', '19'])).
% 0.83/1.02  thf('21', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X2 @ X1 @ X0) = (k2_enumset1 @ X2 @ X1 @ X0 @ X0))),
% 0.83/1.02      inference('demod', [status(thm)], ['13', '14'])).
% 0.83/1.02  thf(t125_enumset1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.02     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ C @ B @ A ) ))).
% 0.83/1.02  thf('22', plain,
% 0.83/1.02      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X24 @ X23 @ X22 @ X21)
% 0.83/1.02           = (k2_enumset1 @ X21 @ X22 @ X23 @ X24))),
% 0.83/1.02      inference('cnf', [status(esa)], [t125_enumset1])).
% 0.83/1.02  thf('23', plain,
% 0.83/1.02      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.83/1.02         ((k2_enumset1 @ X31 @ X31 @ X32 @ X33)
% 0.83/1.02           = (k1_enumset1 @ X31 @ X32 @ X33))),
% 0.83/1.02      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.83/1.02  thf('24', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k1_enumset1 @ X1 @ X1 @ X0)) = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['16', '17'])).
% 0.83/1.02  thf('25', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.83/1.02           = (k2_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['23', '24'])).
% 0.83/1.02  thf('26', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_enumset1 @ X1 @ X0 @ X0 @ X0))
% 0.83/1.02           = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['22', '25'])).
% 0.83/1.02  thf('27', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k1_enumset1 @ X1 @ X0 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['21', '26'])).
% 0.83/1.02  thf('28', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['20', '27'])).
% 0.83/1.02  thf('29', plain,
% 0.83/1.02      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.83/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.02  thf('30', plain,
% 0.83/1.02      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.83/1.02           = (k2_xboole_0 @ (k2_tarski @ X25 @ X26) @ (k1_tarski @ X27)))),
% 0.83/1.02      inference('cnf', [status(esa)], [t43_enumset1])).
% 0.83/1.02  thf('31', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X0 @ X0 @ X1)
% 0.83/1.02           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.83/1.02      inference('sup+', [status(thm)], ['29', '30'])).
% 0.83/1.02  thf('32', plain,
% 0.83/1.02      (![X29 : $i, X30 : $i]:
% 0.83/1.02         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.83/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.83/1.02  thf('33', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.83/1.02           = (k2_tarski @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['31', '32'])).
% 0.83/1.02  thf('34', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.83/1.02           = (k2_tarski @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['28', '33'])).
% 0.83/1.02  thf('35', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.83/1.02           = (k2_tarski @ X1 @ X0))),
% 0.83/1.02      inference('sup+', [status(thm)], ['31', '32'])).
% 0.83/1.02  thf('36', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['34', '35'])).
% 0.83/1.02  thf('37', plain,
% 0.83/1.02      (![X40 : $i, X41 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X40 @ X41)) = (k2_xboole_0 @ X40 @ X41))),
% 0.83/1.02      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.02  thf('38', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['36', '37'])).
% 0.83/1.02  thf('39', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('demod', [status(thm)], ['9', '38'])).
% 0.83/1.02  thf(d8_xboole_0, axiom,
% 0.83/1.02    (![A:$i,B:$i]:
% 0.83/1.02     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.83/1.02       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.83/1.02  thf('40', plain,
% 0.83/1.02      (![X2 : $i, X4 : $i]:
% 0.83/1.02         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.83/1.02      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.83/1.02  thf('41', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (((X1) = (k2_xboole_0 @ X1 @ X0))
% 0.83/1.02          | (r2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['39', '40'])).
% 0.83/1.02  thf('42', plain,
% 0.83/1.02      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.02  thf('43', plain,
% 0.83/1.02      (![X2 : $i, X4 : $i]:
% 0.83/1.02         ((r2_xboole_0 @ X2 @ X4) | ((X2) = (X4)) | ~ (r1_tarski @ X2 @ X4))),
% 0.83/1.02      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.83/1.02  thf('44', plain,
% 0.83/1.02      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))
% 0.83/1.02        | (r2_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B))),
% 0.83/1.02      inference('sup-', [status(thm)], ['42', '43'])).
% 0.83/1.02  thf(antisymmetry_r2_xboole_0, axiom,
% 0.83/1.02    (![A:$i,B:$i]: ( ( r2_xboole_0 @ A @ B ) => ( ~( r2_xboole_0 @ B @ A ) ) ))).
% 0.83/1.02  thf('45', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (~ (r2_xboole_0 @ X0 @ X1) | ~ (r2_xboole_0 @ X1 @ X0))),
% 0.83/1.02      inference('cnf', [status(esa)], [antisymmetry_r2_xboole_0])).
% 0.83/1.02  thf('46', plain,
% 0.83/1.02      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B))
% 0.83/1.02        | ~ (r2_xboole_0 @ sk_B @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['44', '45'])).
% 0.83/1.02  thf('47', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['20', '27'])).
% 0.83/1.02  thf('48', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['20', '27'])).
% 0.83/1.02  thf('49', plain,
% 0.83/1.02      ((((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B))
% 0.83/1.02        | ~ (r2_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.83/1.02      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.83/1.02  thf('50', plain,
% 0.83/1.02      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.83/1.02        | ((k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (sk_B)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['41', '49'])).
% 0.83/1.02  thf('51', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.83/1.02      inference('simplify', [status(thm)], ['50'])).
% 0.83/1.02  thf('52', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.83/1.02         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.83/1.02          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['1', '3'])).
% 0.83/1.02  thf('53', plain,
% 0.83/1.02      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.83/1.02         (((X6) != (X5)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.83/1.02      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.83/1.02  thf('54', plain,
% 0.83/1.02      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X5 @ X7 @ X8 @ X5)),
% 0.83/1.02      inference('simplify', [status(thm)], ['53'])).
% 0.83/1.02  thf('55', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.83/1.02      inference('sup-', [status(thm)], ['52', '54'])).
% 0.83/1.02  thf('56', plain,
% 0.83/1.02      (![X38 : $i, X39 : $i]:
% 0.83/1.02         ((r1_tarski @ X38 @ (k3_tarski @ X39)) | ~ (r2_hidden @ X38 @ X39))),
% 0.83/1.02      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.83/1.02  thf('57', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['55', '56'])).
% 0.83/1.02  thf('58', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('sup+', [status(thm)], ['36', '37'])).
% 0.83/1.02  thf('59', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.83/1.02      inference('demod', [status(thm)], ['57', '58'])).
% 0.83/1.02  thf('60', plain,
% 0.83/1.02      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.83/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.02  thf(t38_zfmisc_1, axiom,
% 0.83/1.02    (![A:$i,B:$i,C:$i]:
% 0.83/1.02     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.83/1.02       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.83/1.02  thf('61', plain,
% 0.83/1.02      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.83/1.02         ((r2_hidden @ X42 @ X43)
% 0.83/1.02          | ~ (r1_tarski @ (k2_tarski @ X42 @ X44) @ X43))),
% 0.83/1.02      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.83/1.02  thf('62', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.83/1.02      inference('sup-', [status(thm)], ['60', '61'])).
% 0.83/1.02  thf('63', plain,
% 0.83/1.02      (![X0 : $i, X1 : $i]:
% 0.83/1.02         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.83/1.02      inference('sup-', [status(thm)], ['59', '62'])).
% 0.83/1.02  thf('64', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.83/1.02      inference('sup+', [status(thm)], ['51', '63'])).
% 0.83/1.02  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 0.83/1.02  
% 0.83/1.02  % SZS output end Refutation
% 0.83/1.02  
% 0.83/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
