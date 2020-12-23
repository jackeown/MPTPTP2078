%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WZbTSv4pes

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:48 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 373 expanded)
%              Number of leaves         :   32 ( 131 expanded)
%              Depth                    :   16
%              Number of atoms          :  716 (2923 expanded)
%              Number of equality atoms :   73 ( 258 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('0',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( k2_enumset1 @ X40 @ X40 @ X41 @ X42 )
      = ( k1_enumset1 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X28 @ X29 @ X30 ) @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X47: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X45 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X45 @ X46 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X45 ) @ ( k1_setfam_1 @ X46 ) ) )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X47: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X47 ) )
      = X47 ) ),
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('18',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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

thf('20',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X13: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ X15 )
      | ( ( k4_xboole_0 @ X13 @ X15 )
       != X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != X1 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

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

thf('41',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('42',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','51'])).

thf('53',plain,(
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('59',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['55','56'])).

thf('61',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('63',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('64',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WZbTSv4pes
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.55/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.55/0.72  % Solved by: fo/fo7.sh
% 0.55/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.72  % done 598 iterations in 0.269s
% 0.55/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.55/0.72  % SZS output start Refutation
% 0.55/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.55/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.72  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.55/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.72  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.72  thf(t71_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i]:
% 0.55/0.72     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.72  thf('0', plain,
% 0.55/0.72      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X40 @ X40 @ X41 @ X42)
% 0.55/0.72           = (k1_enumset1 @ X40 @ X41 @ X42))),
% 0.55/0.72      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.72  thf(t70_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.72  thf('1', plain,
% 0.55/0.72      (![X38 : $i, X39 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.55/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.72  thf('2', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.55/0.72      inference('sup+', [status(thm)], ['0', '1'])).
% 0.55/0.72  thf('3', plain,
% 0.55/0.72      (![X38 : $i, X39 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.55/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.72  thf(t46_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.72     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.55/0.72       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.55/0.72  thf('4', plain,
% 0.55/0.72      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X28 @ X29 @ X30 @ X31)
% 0.55/0.72           = (k2_xboole_0 @ (k1_enumset1 @ X28 @ X29 @ X30) @ (k1_tarski @ X31)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.55/0.72  thf('5', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.55/0.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['3', '4'])).
% 0.55/0.72  thf('6', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((k2_tarski @ X1 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['2', '5'])).
% 0.55/0.72  thf(t69_enumset1, axiom,
% 0.55/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.55/0.72  thf('7', plain, (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf('8', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((k2_tarski @ X1 @ X0)
% 0.55/0.72           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.55/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.55/0.72  thf(t11_setfam_1, axiom,
% 0.55/0.72    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.55/0.72  thf('9', plain, (![X47 : $i]: ((k1_setfam_1 @ (k1_tarski @ X47)) = (X47))),
% 0.55/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.55/0.72  thf(t10_setfam_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.55/0.72          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.55/0.72            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.55/0.72  thf('10', plain,
% 0.55/0.72      (![X45 : $i, X46 : $i]:
% 0.55/0.72         (((X45) = (k1_xboole_0))
% 0.55/0.72          | ((k1_setfam_1 @ (k2_xboole_0 @ X45 @ X46))
% 0.55/0.72              = (k3_xboole_0 @ (k1_setfam_1 @ X45) @ (k1_setfam_1 @ X46)))
% 0.55/0.72          | ((X46) = (k1_xboole_0)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.55/0.72  thf('11', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.55/0.72            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.55/0.72          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.55/0.72          | ((X1) = (k1_xboole_0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['9', '10'])).
% 0.55/0.72  thf('12', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.55/0.72            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.55/0.72          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.55/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['8', '11'])).
% 0.55/0.72  thf('13', plain, (![X47 : $i]: ((k1_setfam_1 @ (k1_tarski @ X47)) = (X47))),
% 0.55/0.72      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.55/0.72  thf('14', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.55/0.72          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.55/0.72          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.55/0.72      inference('demod', [status(thm)], ['12', '13'])).
% 0.55/0.72  thf(t12_setfam_1, conjecture,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.72    (~( ![A:$i,B:$i]:
% 0.55/0.72        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.55/0.72    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.55/0.72  thf('15', plain,
% 0.55/0.72      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.55/0.72         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.72  thf('16', plain,
% 0.55/0.72      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.55/0.72        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.55/0.72        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.55/0.72  thf('17', plain,
% 0.55/0.72      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.55/0.72        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.55/0.72      inference('simplify', [status(thm)], ['16'])).
% 0.55/0.72  thf('18', plain,
% 0.55/0.72      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf('19', plain,
% 0.55/0.72      (![X38 : $i, X39 : $i]:
% 0.55/0.72         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.55/0.72      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.72  thf(d1_enumset1, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.72       ( ![E:$i]:
% 0.55/0.72         ( ( r2_hidden @ E @ D ) <=>
% 0.55/0.72           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.55/0.72  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.55/0.72  thf(zf_stmt_2, axiom,
% 0.55/0.72    (![E:$i,C:$i,B:$i,A:$i]:
% 0.55/0.72     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.55/0.72       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.55/0.72  thf(zf_stmt_3, axiom,
% 0.55/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.72     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.72       ( ![E:$i]:
% 0.55/0.72         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.55/0.72  thf('20', plain,
% 0.55/0.72      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.55/0.72         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.55/0.72          | (r2_hidden @ X21 @ X25)
% 0.55/0.72          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.72  thf('21', plain,
% 0.55/0.72      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.55/0.72         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 0.55/0.72          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.55/0.72      inference('simplify', [status(thm)], ['20'])).
% 0.55/0.72  thf('22', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.55/0.72          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.55/0.72      inference('sup+', [status(thm)], ['19', '21'])).
% 0.55/0.72  thf('23', plain,
% 0.55/0.72      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.55/0.72         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.55/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.72  thf('24', plain,
% 0.55/0.72      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.55/0.72         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 0.55/0.72      inference('simplify', [status(thm)], ['23'])).
% 0.55/0.72  thf('25', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.55/0.72      inference('sup-', [status(thm)], ['22', '24'])).
% 0.55/0.72  thf(t2_boole, axiom,
% 0.55/0.72    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.55/0.72  thf('26', plain,
% 0.55/0.72      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.72  thf(t48_xboole_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.55/0.72  thf('27', plain,
% 0.55/0.72      (![X11 : $i, X12 : $i]:
% 0.55/0.72         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.55/0.72           = (k3_xboole_0 @ X11 @ X12))),
% 0.55/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.72  thf('28', plain,
% 0.55/0.72      (![X11 : $i, X12 : $i]:
% 0.55/0.72         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.55/0.72           = (k3_xboole_0 @ X11 @ X12))),
% 0.55/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.72  thf('29', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.72           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['27', '28'])).
% 0.55/0.72  thf('30', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.55/0.72           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.55/0.72      inference('sup+', [status(thm)], ['26', '29'])).
% 0.55/0.72  thf(t4_xboole_0, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.55/0.72  thf('31', plain,
% 0.55/0.72      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.55/0.72          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.72  thf('32', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.55/0.72          | ~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.72  thf('33', plain,
% 0.55/0.72      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.72  thf('34', plain,
% 0.55/0.72      (![X11 : $i, X12 : $i]:
% 0.55/0.72         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.55/0.72           = (k3_xboole_0 @ X11 @ X12))),
% 0.55/0.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.55/0.72  thf(t83_xboole_1, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.55/0.72  thf('35', plain,
% 0.55/0.72      (![X13 : $i, X15 : $i]:
% 0.55/0.72         ((r1_xboole_0 @ X13 @ X15) | ((k4_xboole_0 @ X13 @ X15) != (X13)))),
% 0.55/0.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.55/0.72  thf('36', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (((k3_xboole_0 @ X1 @ X0) != (X1))
% 0.55/0.72          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.72  thf('37', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         (((k1_xboole_0) != (X0))
% 0.55/0.72          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['33', '36'])).
% 0.55/0.72  thf('38', plain,
% 0.55/0.72      ((r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.55/0.72      inference('simplify', [status(thm)], ['37'])).
% 0.55/0.72  thf(symmetry_r1_xboole_0, axiom,
% 0.55/0.72    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.55/0.72  thf('39', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.55/0.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.55/0.72  thf('40', plain,
% 0.55/0.72      ((r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.55/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.55/0.72  thf(t3_xboole_0, axiom,
% 0.55/0.72    (![A:$i,B:$i]:
% 0.55/0.72     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.55/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.72            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.55/0.72  thf('41', plain,
% 0.55/0.72      (![X2 : $i, X3 : $i]:
% 0.55/0.72         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X3))),
% 0.55/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.72  thf('42', plain,
% 0.55/0.72      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.55/0.72          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.72  thf('43', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.72         ((r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.55/0.72          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.72  thf('44', plain,
% 0.55/0.72      (![X0 : $i]:
% 0.55/0.72         (r1_xboole_0 @ X0 @ 
% 0.55/0.72          (k3_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ 
% 0.55/0.72           k1_xboole_0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['40', '43'])).
% 0.55/0.72  thf('45', plain,
% 0.55/0.72      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.72  thf('46', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.55/0.72      inference('demod', [status(thm)], ['44', '45'])).
% 0.55/0.72  thf('47', plain,
% 0.55/0.72      (![X13 : $i, X14 : $i]:
% 0.55/0.72         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.55/0.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.55/0.72  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.72  thf('49', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.72  thf('50', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.55/0.72      inference('demod', [status(thm)], ['32', '48', '49'])).
% 0.55/0.72  thf('51', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ~ (r1_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['25', '50'])).
% 0.55/0.72  thf('52', plain,
% 0.55/0.72      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['18', '51'])).
% 0.55/0.72  thf('53', plain,
% 0.55/0.72      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.55/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.72  thf('54', plain,
% 0.55/0.72      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.55/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.72  thf('55', plain,
% 0.55/0.72      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.55/0.72        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.55/0.72      inference('sup-', [status(thm)], ['17', '54'])).
% 0.55/0.72  thf('56', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.55/0.72      inference('demod', [status(thm)], ['44', '45'])).
% 0.55/0.72  thf('57', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.55/0.72      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.72  thf('58', plain,
% 0.55/0.72      (![X0 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))),
% 0.55/0.72      inference('demod', [status(thm)], ['52', '53'])).
% 0.55/0.72  thf('59', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.55/0.72      inference('sup-', [status(thm)], ['57', '58'])).
% 0.55/0.72  thf('60', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.55/0.72      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.72  thf('61', plain,
% 0.55/0.72      ((r1_xboole_0 @ (k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.55/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.55/0.72  thf('62', plain,
% 0.55/0.72      (![X2 : $i, X3 : $i]:
% 0.55/0.72         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C @ X3 @ X2) @ X2))),
% 0.55/0.72      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.72  thf('63', plain,
% 0.55/0.72      (![X10 : $i]: ((k3_xboole_0 @ X10 @ k1_xboole_0) = (k1_xboole_0))),
% 0.55/0.72      inference('cnf', [status(esa)], [t2_boole])).
% 0.55/0.72  thf('64', plain,
% 0.55/0.72      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 0.55/0.72          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.55/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.55/0.72  thf('65', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['63', '64'])).
% 0.55/0.72  thf('66', plain,
% 0.55/0.72      (![X0 : $i, X1 : $i]:
% 0.55/0.72         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.55/0.72      inference('sup-', [status(thm)], ['62', '65'])).
% 0.55/0.72  thf('67', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.55/0.72      inference('sup-', [status(thm)], ['61', '66'])).
% 0.55/0.72  thf('68', plain, ($false),
% 0.55/0.72      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.55/0.72  
% 0.55/0.72  % SZS output end Refutation
% 0.55/0.72  
% 0.55/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
