%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lWnrystGSg

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:46 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 269 expanded)
%              Number of leaves         :   31 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  641 (2130 expanded)
%              Number of equality atoms :   70 ( 193 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_enumset1 @ X33 @ X33 @ X34 )
      = ( k2_tarski @ X33 @ X34 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X42: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X40: $i,X41: $i] :
      ( ( X40 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X40 @ X41 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X40 ) @ ( k1_setfam_1 @ X41 ) ) )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X42: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X32: $i] :
      ( ( k2_tarski @ X32 @ X32 )
      = ( k1_tarski @ X32 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

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

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('36',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X14 )
      | ( ( k4_xboole_0 @ X12 @ X14 )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['23','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('49',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('50',plain,(
    ! [X42: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X42 ) )
      = X42 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('51',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference('sup-',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( k1_setfam_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('62',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference('sup-',[status(thm)],['6','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lWnrystGSg
% 0.14/0.36  % Computer   : n004.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 16:03:39 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.53/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.72  % Solved by: fo/fo7.sh
% 0.53/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.72  % done 289 iterations in 0.256s
% 0.53/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.72  % SZS output start Refutation
% 0.53/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.53/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.53/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.53/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.53/0.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.53/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.53/0.72  thf(t70_enumset1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.53/0.72  thf('0', plain,
% 0.53/0.72      (![X33 : $i, X34 : $i]:
% 0.53/0.72         ((k1_enumset1 @ X33 @ X33 @ X34) = (k2_tarski @ X33 @ X34))),
% 0.53/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.53/0.72  thf(d1_enumset1, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.72       ( ![E:$i]:
% 0.53/0.72         ( ( r2_hidden @ E @ D ) <=>
% 0.53/0.72           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.53/0.72  thf(zf_stmt_1, axiom,
% 0.53/0.72    (![E:$i,C:$i,B:$i,A:$i]:
% 0.53/0.72     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.53/0.72       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.53/0.72  thf(zf_stmt_2, axiom,
% 0.53/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.53/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.53/0.72       ( ![E:$i]:
% 0.53/0.72         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.53/0.72  thf('1', plain,
% 0.53/0.72      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.72         ((zip_tseitin_0 @ X20 @ X21 @ X22 @ X23)
% 0.53/0.72          | (r2_hidden @ X20 @ X24)
% 0.53/0.72          | ((X24) != (k1_enumset1 @ X23 @ X22 @ X21)))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.53/0.72  thf('2', plain,
% 0.53/0.72      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.72         ((r2_hidden @ X20 @ (k1_enumset1 @ X23 @ X22 @ X21))
% 0.53/0.72          | (zip_tseitin_0 @ X20 @ X21 @ X22 @ X23))),
% 0.53/0.72      inference('simplify', [status(thm)], ['1'])).
% 0.53/0.72  thf('3', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.53/0.72          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.53/0.72      inference('sup+', [status(thm)], ['0', '2'])).
% 0.53/0.72  thf('4', plain,
% 0.53/0.72      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.53/0.72         (((X16) != (X15)) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.53/0.72  thf('5', plain,
% 0.53/0.72      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.53/0.72         ~ (zip_tseitin_0 @ X15 @ X17 @ X18 @ X15)),
% 0.53/0.72      inference('simplify', [status(thm)], ['4'])).
% 0.53/0.72  thf('6', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['3', '5'])).
% 0.53/0.72  thf('7', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['3', '5'])).
% 0.53/0.72  thf(t41_enumset1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k2_tarski @ A @ B ) =
% 0.53/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.53/0.72  thf('8', plain,
% 0.53/0.72      (![X27 : $i, X28 : $i]:
% 0.53/0.72         ((k2_tarski @ X27 @ X28)
% 0.53/0.72           = (k2_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X28)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.53/0.72  thf(t11_setfam_1, axiom,
% 0.53/0.72    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.53/0.72  thf('9', plain, (![X42 : $i]: ((k1_setfam_1 @ (k1_tarski @ X42)) = (X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.53/0.72  thf(t10_setfam_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.53/0.72          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.53/0.72            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.53/0.72  thf('10', plain,
% 0.53/0.72      (![X40 : $i, X41 : $i]:
% 0.53/0.72         (((X40) = (k1_xboole_0))
% 0.53/0.72          | ((k1_setfam_1 @ (k2_xboole_0 @ X40 @ X41))
% 0.53/0.72              = (k3_xboole_0 @ (k1_setfam_1 @ X40) @ (k1_setfam_1 @ X41)))
% 0.53/0.72          | ((X41) = (k1_xboole_0)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.53/0.72  thf('11', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.53/0.72            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.53/0.72          | ((X1) = (k1_xboole_0))
% 0.53/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['9', '10'])).
% 0.53/0.72  thf('12', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.53/0.72            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.53/0.72          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.53/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['8', '11'])).
% 0.53/0.72  thf('13', plain, (![X42 : $i]: ((k1_setfam_1 @ (k1_tarski @ X42)) = (X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.53/0.72  thf('14', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.53/0.72          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.53/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.53/0.72      inference('demod', [status(thm)], ['12', '13'])).
% 0.53/0.72  thf(t12_setfam_1, conjecture,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.72  thf(zf_stmt_3, negated_conjecture,
% 0.53/0.72    (~( ![A:$i,B:$i]:
% 0.53/0.72        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.53/0.72    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.53/0.72  thf('15', plain,
% 0.53/0.72      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.53/0.72         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.53/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.53/0.72  thf('16', plain,
% 0.53/0.72      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.53/0.72        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.53/0.72        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.72  thf('17', plain,
% 0.53/0.72      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.53/0.72        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['16'])).
% 0.53/0.72  thf(t69_enumset1, axiom,
% 0.53/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.53/0.72  thf('18', plain,
% 0.53/0.72      (![X32 : $i]: ((k2_tarski @ X32 @ X32) = (k1_tarski @ X32))),
% 0.53/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.53/0.72  thf('19', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['3', '5'])).
% 0.53/0.72  thf(t3_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.53/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.53/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.53/0.72            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.53/0.72  thf('20', plain,
% 0.53/0.72      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X2 @ X0)
% 0.53/0.72          | ~ (r2_hidden @ X2 @ X3)
% 0.53/0.72          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.72  thf('21', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.53/0.72          | ~ (r2_hidden @ X1 @ X2))),
% 0.53/0.72      inference('sup-', [status(thm)], ['19', '20'])).
% 0.53/0.72  thf('22', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['18', '21'])).
% 0.53/0.72  thf('23', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.72          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.53/0.72          | ~ (r2_hidden @ sk_B @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['17', '22'])).
% 0.53/0.72  thf(t17_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.72  thf('24', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.53/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.72  thf(t2_boole, axiom,
% 0.53/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.53/0.72  thf('25', plain,
% 0.53/0.72      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.53/0.72  thf('26', plain,
% 0.53/0.72      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 0.53/0.72      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.53/0.72  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.53/0.72      inference('sup+', [status(thm)], ['25', '26'])).
% 0.53/0.72  thf(d10_xboole_0, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.72  thf('28', plain,
% 0.53/0.72      (![X4 : $i, X6 : $i]:
% 0.53/0.72         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.53/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.72  thf('29', plain,
% 0.53/0.72      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.72  thf('30', plain,
% 0.53/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['24', '29'])).
% 0.53/0.72  thf(t48_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.53/0.72  thf('31', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.53/0.72           = (k3_xboole_0 @ X10 @ X11))),
% 0.53/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.72  thf('32', plain,
% 0.53/0.72      (![X10 : $i, X11 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.53/0.72           = (k3_xboole_0 @ X10 @ X11))),
% 0.53/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.53/0.72  thf('33', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.53/0.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['31', '32'])).
% 0.53/0.72  thf('34', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         ((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 0.53/0.72           = (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['30', '33'])).
% 0.53/0.72  thf('35', plain,
% 0.53/0.72      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['24', '29'])).
% 0.53/0.72  thf('36', plain,
% 0.53/0.72      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.53/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.53/0.72  thf(t83_xboole_1, axiom,
% 0.53/0.72    (![A:$i,B:$i]:
% 0.53/0.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.53/0.72  thf('37', plain,
% 0.53/0.72      (![X12 : $i, X14 : $i]:
% 0.53/0.72         ((r1_xboole_0 @ X12 @ X14) | ((k4_xboole_0 @ X12 @ X14) != (X12)))),
% 0.53/0.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.53/0.72  thf('38', plain,
% 0.53/0.72      ((((k1_xboole_0) != (k1_xboole_0))
% 0.53/0.72        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.72  thf('39', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.53/0.72      inference('simplify', [status(thm)], ['38'])).
% 0.53/0.72  thf('40', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.72  thf('41', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.53/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.72  thf('42', plain,
% 0.53/0.72      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.53/0.72         (~ (r2_hidden @ X2 @ X0)
% 0.53/0.72          | ~ (r2_hidden @ X2 @ X3)
% 0.53/0.72          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.53/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.53/0.72  thf('43', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.72         ((r1_xboole_0 @ X0 @ X1)
% 0.53/0.72          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.53/0.72          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.53/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.53/0.72  thf('44', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         ((r1_xboole_0 @ X0 @ X1)
% 0.53/0.72          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.53/0.72          | (r1_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['40', '43'])).
% 0.53/0.72  thf('45', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.53/0.72      inference('simplify', [status(thm)], ['44'])).
% 0.53/0.72  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.53/0.72      inference('sup-', [status(thm)], ['39', '45'])).
% 0.53/0.72  thf('47', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k1_tarski @ sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['23', '46'])).
% 0.53/0.72  thf('48', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['3', '5'])).
% 0.53/0.72  thf('49', plain,
% 0.53/0.72      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.53/0.72        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.53/0.72      inference('simplify', [status(thm)], ['16'])).
% 0.53/0.72  thf('50', plain, (![X42 : $i]: ((k1_setfam_1 @ (k1_tarski @ X42)) = (X42))),
% 0.53/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.53/0.72  thf('51', plain,
% 0.53/0.72      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.53/0.72        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.53/0.72      inference('sup+', [status(thm)], ['49', '50'])).
% 0.53/0.72  thf('52', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['18', '21'])).
% 0.53/0.72  thf('53', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.53/0.72          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.53/0.72          | ~ (r2_hidden @ sk_A @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['51', '52'])).
% 0.53/0.72  thf('54', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.53/0.72      inference('sup-', [status(thm)], ['39', '45'])).
% 0.53/0.72  thf('55', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k1_setfam_1 @ k1_xboole_0) = (sk_B)) | ~ (r2_hidden @ sk_A @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['53', '54'])).
% 0.53/0.72  thf('56', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.53/0.72      inference('sup-', [status(thm)], ['48', '55'])).
% 0.53/0.72  thf('57', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.53/0.72          | ~ (r2_hidden @ (k1_setfam_1 @ k1_xboole_0) @ X0))),
% 0.53/0.72      inference('demod', [status(thm)], ['47', '56'])).
% 0.53/0.72  thf('58', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['7', '57'])).
% 0.53/0.72  thf('59', plain,
% 0.53/0.72      (![X0 : $i, X1 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.53/0.72      inference('sup-', [status(thm)], ['18', '21'])).
% 0.53/0.72  thf('60', plain,
% 0.53/0.72      (![X0 : $i]:
% 0.53/0.72         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.53/0.72      inference('sup-', [status(thm)], ['58', '59'])).
% 0.53/0.72  thf('61', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.53/0.72      inference('sup-', [status(thm)], ['39', '45'])).
% 0.53/0.72  thf('62', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.53/0.72      inference('demod', [status(thm)], ['60', '61'])).
% 0.53/0.72  thf('63', plain, ($false), inference('sup-', [status(thm)], ['6', '62'])).
% 0.53/0.72  
% 0.53/0.72  % SZS output end Refutation
% 0.53/0.72  
% 0.53/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
