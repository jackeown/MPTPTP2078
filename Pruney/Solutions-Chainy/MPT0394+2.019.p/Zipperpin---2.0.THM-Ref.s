%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xJCXIh5ydW

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:47 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 153 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :   17
%              Number of atoms          :  700 (1292 expanded)
%              Number of equality atoms :   70 ( 110 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf('10',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t44_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( k2_enumset1 @ X20 @ X21 @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_enumset1 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t44_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X3 ) @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t47_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ) )).

thf('14',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28 )
      = ( k2_xboole_0 @ ( k1_tarski @ X24 ) @ ( k2_enumset1 @ X25 @ X26 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t47_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X29 @ X30 @ X31 @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X1 @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','25'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('27',plain,(
    ! [X44: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('28',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X42 @ X43 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X42 ) @ ( k1_setfam_1 @ X43 ) ) )
      | ( X43 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X44: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('33',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

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

thf('38',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','52'])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['8','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xJCXIh5ydW
% 0.16/0.36  % Computer   : n006.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 18:55:23 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.59/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.80  % Solved by: fo/fo7.sh
% 0.59/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.80  % done 651 iterations in 0.328s
% 0.59/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.80  % SZS output start Refutation
% 0.59/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.80  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.80  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.59/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.59/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.80  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.59/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.59/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.80  thf(t69_enumset1, axiom,
% 0.59/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.80  thf('0', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf(t70_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.80  thf('1', plain,
% 0.59/0.80      (![X35 : $i, X36 : $i]:
% 0.59/0.80         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.59/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.80  thf(d1_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.80       ( ![E:$i]:
% 0.59/0.80         ( ( r2_hidden @ E @ D ) <=>
% 0.59/0.80           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.59/0.80  thf(zf_stmt_1, axiom,
% 0.59/0.80    (![E:$i,C:$i,B:$i,A:$i]:
% 0.59/0.80     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.59/0.80       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.59/0.80  thf(zf_stmt_2, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.80       ( ![E:$i]:
% 0.59/0.80         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.59/0.80  thf('2', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.80         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.59/0.80          | (r2_hidden @ X13 @ X17)
% 0.59/0.80          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.59/0.80  thf('3', plain,
% 0.59/0.80      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.80         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.59/0.80          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.59/0.80      inference('simplify', [status(thm)], ['2'])).
% 0.59/0.80  thf('4', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.80          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.59/0.80      inference('sup+', [status(thm)], ['1', '3'])).
% 0.59/0.80  thf('5', plain,
% 0.59/0.80      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.80         (((X9) != (X8)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.59/0.80  thf('6', plain,
% 0.59/0.80      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X8 @ X10 @ X11 @ X8)),
% 0.59/0.80      inference('simplify', [status(thm)], ['5'])).
% 0.59/0.80  thf('7', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['4', '6'])).
% 0.59/0.80  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['0', '7'])).
% 0.59/0.80  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['0', '7'])).
% 0.59/0.80  thf('10', plain,
% 0.59/0.80      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf(t71_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i]:
% 0.59/0.80     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.59/0.80  thf('11', plain,
% 0.59/0.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.59/0.80           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf(t44_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.80     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_enumset1 @ B @ C @ D ) ) ))).
% 0.59/0.80  thf('12', plain,
% 0.59/0.80      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X20 @ X21 @ X22 @ X23)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k1_enumset1 @ X21 @ X22 @ X23)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t44_enumset1])).
% 0.59/0.80  thf('13', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X3) @ 
% 0.59/0.80              (k2_enumset1 @ X2 @ X2 @ X1 @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.59/0.80  thf(t47_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.80     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_enumset1 @ B @ C @ D @ E ) ) ))).
% 0.59/0.80  thf('14', plain,
% 0.59/0.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X24 @ X25 @ X26 @ X27 @ X28)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X24) @ 
% 0.59/0.80              (k2_enumset1 @ X25 @ X26 @ X27 @ X28)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t47_enumset1])).
% 0.59/0.80  thf('15', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0)
% 0.59/0.80           = (k3_enumset1 @ X3 @ X2 @ X2 @ X1 @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['13', '14'])).
% 0.59/0.80  thf('16', plain,
% 0.59/0.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.59/0.80           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf('17', plain,
% 0.59/0.80      (![X35 : $i, X36 : $i]:
% 0.59/0.80         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.59/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.80  thf('18', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['16', '17'])).
% 0.59/0.80  thf('19', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.59/0.80      inference('sup+', [status(thm)], ['15', '18'])).
% 0.59/0.80  thf('20', plain,
% 0.59/0.80      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.80         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.59/0.80           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.59/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.59/0.80  thf(t50_enumset1, axiom,
% 0.59/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.80     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.59/0.80       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.59/0.80  thf('21', plain,
% 0.59/0.80      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.59/0.80           = (k2_xboole_0 @ (k2_enumset1 @ X29 @ X30 @ X31 @ X32) @ 
% 0.59/0.80              (k1_tarski @ X33)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.59/0.80  thf('22', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.80         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.59/0.80           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['20', '21'])).
% 0.59/0.80  thf('23', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X1 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k1_enumset1 @ X1 @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['19', '22'])).
% 0.59/0.80  thf('24', plain,
% 0.59/0.80      (![X35 : $i, X36 : $i]:
% 0.59/0.80         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.59/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.80  thf('25', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X1 @ X0)
% 0.59/0.80           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.59/0.80      inference('demod', [status(thm)], ['23', '24'])).
% 0.59/0.80  thf('26', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((k2_tarski @ X0 @ X1)
% 0.59/0.80           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['10', '25'])).
% 0.59/0.80  thf(t11_setfam_1, axiom,
% 0.59/0.80    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.59/0.80  thf('27', plain, (![X44 : $i]: ((k1_setfam_1 @ (k1_tarski @ X44)) = (X44))),
% 0.59/0.80      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.59/0.80  thf(t10_setfam_1, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.80          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.59/0.80            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.59/0.80  thf('28', plain,
% 0.59/0.80      (![X42 : $i, X43 : $i]:
% 0.59/0.80         (((X42) = (k1_xboole_0))
% 0.59/0.80          | ((k1_setfam_1 @ (k2_xboole_0 @ X42 @ X43))
% 0.59/0.80              = (k3_xboole_0 @ (k1_setfam_1 @ X42) @ (k1_setfam_1 @ X43)))
% 0.59/0.80          | ((X43) = (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.59/0.80  thf('29', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.59/0.80            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.59/0.80          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.59/0.80          | ((X1) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['27', '28'])).
% 0.59/0.80  thf('30', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.59/0.80            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.59/0.80          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.59/0.80          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup+', [status(thm)], ['26', '29'])).
% 0.59/0.80  thf('31', plain, (![X44 : $i]: ((k1_setfam_1 @ (k1_tarski @ X44)) = (X44))),
% 0.59/0.80      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.59/0.80  thf('32', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.59/0.80          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.59/0.80          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.59/0.80      inference('demod', [status(thm)], ['30', '31'])).
% 0.59/0.80  thf(t12_setfam_1, conjecture,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.80  thf(zf_stmt_3, negated_conjecture,
% 0.59/0.80    (~( ![A:$i,B:$i]:
% 0.59/0.80        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.59/0.80    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.59/0.80  thf('33', plain,
% 0.59/0.80      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.59/0.80         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.59/0.80  thf('34', plain,
% 0.59/0.80      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.59/0.80        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.59/0.80        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.80  thf('35', plain,
% 0.59/0.80      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.59/0.80        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['34'])).
% 0.59/0.80  thf('36', plain,
% 0.59/0.80      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.59/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.80  thf('37', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['4', '6'])).
% 0.59/0.80  thf(t3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.80  thf('38', plain,
% 0.59/0.80      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.59/0.80          | ~ (r2_hidden @ X6 @ X7)
% 0.59/0.80          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('39', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)
% 0.59/0.80          | ~ (r2_hidden @ X1 @ X2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.80  thf('40', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['36', '39'])).
% 0.59/0.80  thf('41', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.59/0.80          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.59/0.80          | ~ (r2_hidden @ sk_B @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['35', '40'])).
% 0.59/0.80  thf(idempotence_k3_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.59/0.80  thf('42', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.59/0.80      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.59/0.80  thf(d7_xboole_0, axiom,
% 0.59/0.80    (![A:$i,B:$i]:
% 0.59/0.80     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.80       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.80  thf('43', plain,
% 0.59/0.80      (![X0 : $i, X2 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.59/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.80  thf('44', plain,
% 0.59/0.80      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.80  thf('45', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.59/0.80      inference('simplify', [status(thm)], ['44'])).
% 0.59/0.80  thf('46', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('47', plain,
% 0.59/0.80      (![X4 : $i, X5 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('48', plain,
% 0.59/0.80      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.59/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.59/0.80          | ~ (r2_hidden @ X6 @ X7)
% 0.59/0.80          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.59/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.80  thf('49', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.59/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.59/0.80          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.59/0.80      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.80  thf('50', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.59/0.80          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.59/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['46', '49'])).
% 0.59/0.80  thf('51', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.59/0.80      inference('simplify', [status(thm)], ['50'])).
% 0.59/0.80  thf('52', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.59/0.80      inference('sup-', [status(thm)], ['45', '51'])).
% 0.59/0.80  thf('53', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (((k1_tarski @ sk_A) = (k1_xboole_0)) | ~ (r2_hidden @ sk_B @ X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['41', '52'])).
% 0.59/0.80  thf('54', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['9', '53'])).
% 0.59/0.80  thf('55', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.59/0.80      inference('sup-', [status(thm)], ['36', '39'])).
% 0.59/0.80  thf('56', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['54', '55'])).
% 0.59/0.80  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.59/0.80      inference('sup-', [status(thm)], ['45', '51'])).
% 0.59/0.80  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.59/0.80      inference('demod', [status(thm)], ['56', '57'])).
% 0.59/0.80  thf('59', plain, ($false), inference('sup-', [status(thm)], ['8', '58'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
