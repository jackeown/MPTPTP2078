%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t2Mr6QbxzW

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:38 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 200 expanded)
%              Number of leaves         :   27 (  72 expanded)
%              Depth                    :   23
%              Number of atoms          :  737 (1649 expanded)
%              Number of equality atoms :   65 ( 129 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
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

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 )
      | ( r2_hidden @ X20 @ X24 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('2',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 != X15 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ~ ( zip_tseitin_0 @ X15 @ X17 @ X18 @ X15 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( X16 = X17 )
      | ( X16 = X18 )
      | ( X16 = X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('10',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k4_xboole_0 @ X10 @ X11 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('34',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['16','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['10','52'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('54',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('55',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('58',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ( X24
       != ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X25 @ X21 @ X22 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_enumset1 @ X23 @ X22 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','62'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','64'])).

thf('66',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('68',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X27: $i] :
      ( ( k2_tarski @ X27 @ X27 )
      = ( k1_tarski @ X27 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('71',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('76',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t2Mr6QbxzW
% 0.14/0.35  % Computer   : n021.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:36:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.75  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.75  % Solved by: fo/fo7.sh
% 0.54/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.75  % done 608 iterations in 0.279s
% 0.54/0.75  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.75  % SZS output start Refutation
% 0.54/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.75  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.75  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.54/0.75  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.54/0.75  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.54/0.75  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.54/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.75  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.54/0.75  thf(t70_enumset1, axiom,
% 0.54/0.75    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.54/0.75  thf('0', plain,
% 0.54/0.75      (![X28 : $i, X29 : $i]:
% 0.54/0.75         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.54/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.75  thf(d1_enumset1, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.75       ( ![E:$i]:
% 0.54/0.75         ( ( r2_hidden @ E @ D ) <=>
% 0.54/0.75           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.54/0.75  thf(zf_stmt_1, axiom,
% 0.54/0.75    (![E:$i,C:$i,B:$i,A:$i]:
% 0.54/0.75     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.54/0.75       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.54/0.75  thf(zf_stmt_2, axiom,
% 0.54/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.75     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.54/0.75       ( ![E:$i]:
% 0.54/0.75         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.54/0.75  thf('1', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.54/0.75         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.54/0.75          | (r2_hidden @ X20 @ X24)
% 0.54/0.75          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.75  thf('2', plain,
% 0.54/0.75      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.75         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.54/0.75          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.54/0.75      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.75  thf('3', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.54/0.75          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.54/0.75      inference('sup+', [status(thm)], ['0', '2'])).
% 0.54/0.75  thf('4', plain,
% 0.54/0.75      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.54/0.75         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf('5', plain,
% 0.54/0.75      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.54/0.75         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.54/0.75      inference('simplify', [status(thm)], ['4'])).
% 0.54/0.75  thf('6', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['3', '5'])).
% 0.54/0.75  thf('7', plain,
% 0.54/0.75      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.54/0.75         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.54/0.75          | ((X16) = (X17))
% 0.54/0.75          | ((X16) = (X18))
% 0.54/0.75          | ((X16) = (X19)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.54/0.75  thf(t18_zfmisc_1, conjecture,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.54/0.75         ( k1_tarski @ A ) ) =>
% 0.54/0.75       ( ( A ) = ( B ) ) ))).
% 0.54/0.75  thf(zf_stmt_3, negated_conjecture,
% 0.54/0.75    (~( ![A:$i,B:$i]:
% 0.54/0.75        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.54/0.75            ( k1_tarski @ A ) ) =>
% 0.54/0.75          ( ( A ) = ( B ) ) ) )),
% 0.54/0.75    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.54/0.75  thf('8', plain,
% 0.54/0.75      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.54/0.75         = (k1_tarski @ sk_A))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.75  thf(t47_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('9', plain,
% 0.54/0.75      (![X6 : $i, X7 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.54/0.75           = (k4_xboole_0 @ X6 @ X7))),
% 0.54/0.75      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.54/0.75  thf('10', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.54/0.75         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['8', '9'])).
% 0.54/0.75  thf(t2_boole, axiom,
% 0.54/0.75    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.75  thf('11', plain,
% 0.54/0.75      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.75  thf(t48_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.54/0.75  thf('12', plain,
% 0.54/0.75      (![X8 : $i, X9 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.54/0.75           = (k3_xboole_0 @ X8 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.75  thf(t83_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.75  thf('13', plain,
% 0.54/0.75      (![X12 : $i, X14 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.54/0.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.75  thf('14', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.54/0.75          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['12', '13'])).
% 0.54/0.75  thf('15', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (((k1_xboole_0) != (X0))
% 0.54/0.75          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['11', '14'])).
% 0.54/0.75  thf('16', plain,
% 0.54/0.75      ((r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['15'])).
% 0.54/0.75  thf('17', plain,
% 0.54/0.75      ((r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['15'])).
% 0.54/0.75  thf(t3_xboole_0, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.54/0.75            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.54/0.75       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.54/0.75            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.54/0.75  thf('18', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('19', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('20', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X2 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X2 @ X3)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('21', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X1 @ X0)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.54/0.75          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('22', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1)
% 0.54/0.75          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.54/0.75          | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['18', '21'])).
% 0.54/0.75  thf('23', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['22'])).
% 0.54/0.75  thf('24', plain,
% 0.54/0.75      ((r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['17', '23'])).
% 0.54/0.75  thf('25', plain,
% 0.54/0.75      (![X12 : $i, X13 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.75  thf('26', plain,
% 0.54/0.75      (((k4_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)
% 0.54/0.75         = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.75  thf(t51_xboole_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 0.54/0.75       ( A ) ))).
% 0.54/0.75  thf('27', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 0.54/0.75           = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.54/0.75  thf('28', plain,
% 0.54/0.75      (((k2_xboole_0 @ 
% 0.54/0.75         (k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.54/0.75         (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.54/0.75         = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['26', '27'])).
% 0.54/0.75  thf('29', plain,
% 0.54/0.75      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.75  thf('30', plain,
% 0.54/0.75      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.75  thf('31', plain,
% 0.54/0.75      (![X10 : $i, X11 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k4_xboole_0 @ X10 @ X11))
% 0.54/0.75           = (X10))),
% 0.54/0.75      inference('cnf', [status(esa)], [t51_xboole_1])).
% 0.54/0.75  thf('32', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         ((k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['30', '31'])).
% 0.54/0.75  thf('33', plain,
% 0.54/0.75      (((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.54/0.75  thf('34', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.54/0.75      inference('demod', [status(thm)], ['16', '33'])).
% 0.54/0.75  thf('35', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('36', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('37', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X2 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X2 @ X3)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('38', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.54/0.75          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.54/0.75  thf('39', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.54/0.75          | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['35', '38'])).
% 0.54/0.75  thf('40', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.54/0.75      inference('simplify', [status(thm)], ['39'])).
% 0.54/0.75  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['34', '40'])).
% 0.54/0.75  thf('42', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('43', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X1 @ X0)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.54/0.75          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.54/0.75      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.75  thf('44', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ X1 @ X0)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.54/0.75          | (r1_xboole_0 @ X1 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['42', '43'])).
% 0.54/0.75  thf('45', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X1 @ X0))),
% 0.54/0.75      inference('simplify', [status(thm)], ['44'])).
% 0.54/0.75  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['41', '45'])).
% 0.54/0.75  thf('47', plain,
% 0.54/0.75      (![X12 : $i, X13 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.75  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.75  thf('49', plain,
% 0.54/0.75      (![X8 : $i, X9 : $i]:
% 0.54/0.75         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.54/0.75           = (k3_xboole_0 @ X8 @ X9))),
% 0.54/0.75      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.54/0.75  thf('50', plain,
% 0.54/0.75      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['48', '49'])).
% 0.54/0.75  thf('51', plain,
% 0.54/0.75      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.75      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.75  thf('52', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.54/0.75      inference('demod', [status(thm)], ['50', '51'])).
% 0.54/0.75  thf('53', plain,
% 0.54/0.75      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.54/0.75      inference('demod', [status(thm)], ['10', '52'])).
% 0.54/0.75  thf(l27_zfmisc_1, axiom,
% 0.54/0.75    (![A:$i,B:$i]:
% 0.54/0.75     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.54/0.75  thf('54', plain,
% 0.54/0.75      (![X33 : $i, X34 : $i]:
% 0.54/0.75         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 0.54/0.75      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.54/0.75  thf('55', plain,
% 0.54/0.75      (![X12 : $i, X13 : $i]:
% 0.54/0.75         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.54/0.75      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.54/0.75  thf('56', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         ((r2_hidden @ X1 @ X0)
% 0.54/0.75          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.75  thf('57', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.54/0.75        | (r2_hidden @ sk_A @ (k1_tarski @ sk_B)))),
% 0.54/0.75      inference('sup+', [status(thm)], ['53', '56'])).
% 0.54/0.75  thf(t69_enumset1, axiom,
% 0.54/0.75    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.54/0.75  thf('58', plain,
% 0.54/0.75      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf('59', plain,
% 0.54/0.75      (![X28 : $i, X29 : $i]:
% 0.54/0.75         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.54/0.75      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.54/0.75  thf('60', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X25 @ X24)
% 0.54/0.75          | ~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.54/0.75          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.54/0.75  thf('61', plain,
% 0.54/0.75      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.54/0.75         (~ (zip_tseitin_0 @ X25 @ X21 @ X22 @ X23)
% 0.54/0.75          | ~ (r2_hidden @ X25 @ (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['60'])).
% 0.54/0.75  thf('62', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.54/0.75          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['59', '61'])).
% 0.54/0.75  thf('63', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.54/0.75          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['58', '62'])).
% 0.54/0.75  thf('64', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k1_tarski @ sk_A))
% 0.54/0.75        | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B))),
% 0.54/0.75      inference('sup-', [status(thm)], ['57', '63'])).
% 0.54/0.75  thf('65', plain,
% 0.54/0.75      ((((sk_A) = (sk_B))
% 0.54/0.75        | ((sk_A) = (sk_B))
% 0.54/0.75        | ((sk_A) = (sk_B))
% 0.54/0.75        | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 0.54/0.75      inference('sup-', [status(thm)], ['7', '64'])).
% 0.54/0.75  thf('66', plain,
% 0.54/0.75      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_A) = (sk_B)))),
% 0.54/0.75      inference('simplify', [status(thm)], ['65'])).
% 0.54/0.75  thf('67', plain, (((sk_A) != (sk_B))),
% 0.54/0.75      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.54/0.75  thf('68', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.54/0.75      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.54/0.75  thf('69', plain,
% 0.54/0.75      (![X27 : $i]: ((k2_tarski @ X27 @ X27) = (k1_tarski @ X27))),
% 0.54/0.75      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.54/0.75  thf('70', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['3', '5'])).
% 0.54/0.75  thf('71', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.54/0.75      inference('sup+', [status(thm)], ['69', '70'])).
% 0.54/0.75  thf('72', plain,
% 0.54/0.75      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.54/0.75         (~ (r2_hidden @ X2 @ X0)
% 0.54/0.75          | ~ (r2_hidden @ X2 @ X3)
% 0.54/0.75          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.54/0.75      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.54/0.75  thf('73', plain,
% 0.54/0.75      (![X0 : $i, X1 : $i]:
% 0.54/0.75         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.54/0.75      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.75  thf('74', plain,
% 0.54/0.75      (![X0 : $i]:
% 0.54/0.75         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.54/0.75      inference('sup-', [status(thm)], ['68', '73'])).
% 0.54/0.75  thf('75', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.54/0.75      inference('sup-', [status(thm)], ['34', '40'])).
% 0.54/0.75  thf('76', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.54/0.75      inference('demod', [status(thm)], ['74', '75'])).
% 0.54/0.75  thf('77', plain, ($false), inference('sup-', [status(thm)], ['6', '76'])).
% 0.54/0.75  
% 0.54/0.75  % SZS output end Refutation
% 0.54/0.75  
% 0.54/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
