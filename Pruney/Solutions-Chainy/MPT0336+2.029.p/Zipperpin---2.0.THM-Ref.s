%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gJRpwDga6x

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:23 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 133 expanded)
%              Number of leaves         :   34 (  53 expanded)
%              Depth                    :   23
%              Number of atoms          :  684 ( 974 expanded)
%              Number of equality atoms :   69 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X45: $i,X46: $i] :
      ( ( X46
        = ( k1_tarski @ X45 ) )
      | ( X46 = k1_xboole_0 )
      | ~ ( r1_tarski @ X46 @ ( k1_tarski @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('20',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X11 @ X12 ) @ X13 )
      = ( k3_xboole_0 @ X11 @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('32',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_tarski @ sk_D ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('39',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('51',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['50','51'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('53',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( ( k3_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
        = ( k3_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) )
      = ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','65'])).

thf('67',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gJRpwDga6x
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:30:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.29  % Solved by: fo/fo7.sh
% 1.07/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.29  % done 2036 iterations in 0.834s
% 1.07/1.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.29  % SZS output start Refutation
% 1.07/1.29  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.07/1.29  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.07/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.29  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.07/1.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.29  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.29  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.07/1.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.07/1.29  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.07/1.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.29  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.29  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.07/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.29  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.07/1.29  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.07/1.29  thf(t149_zfmisc_1, conjecture,
% 1.07/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.29     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.07/1.29         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.07/1.29       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.07/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.29    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.29        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.07/1.29            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.07/1.29          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.07/1.29    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.07/1.29  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf(d7_xboole_0, axiom,
% 1.07/1.29    (![A:$i,B:$i]:
% 1.07/1.29     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.07/1.29       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.07/1.29  thf('2', plain,
% 1.07/1.29      (![X2 : $i, X3 : $i]:
% 1.07/1.29         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.07/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.29  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.07/1.29      inference('sup-', [status(thm)], ['1', '2'])).
% 1.07/1.29  thf(commutativity_k3_xboole_0, axiom,
% 1.07/1.29    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.07/1.29  thf('4', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.29  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.29  thf('6', plain,
% 1.07/1.29      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.07/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.29  thf('7', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.29  thf('8', plain,
% 1.07/1.29      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.07/1.29      inference('demod', [status(thm)], ['6', '7'])).
% 1.07/1.29  thf(l3_zfmisc_1, axiom,
% 1.07/1.29    (![A:$i,B:$i]:
% 1.07/1.29     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.07/1.29       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.07/1.29  thf('9', plain,
% 1.07/1.29      (![X45 : $i, X46 : $i]:
% 1.07/1.29         (((X46) = (k1_tarski @ X45))
% 1.07/1.29          | ((X46) = (k1_xboole_0))
% 1.07/1.29          | ~ (r1_tarski @ X46 @ (k1_tarski @ X45)))),
% 1.07/1.29      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.07/1.29  thf('10', plain,
% 1.07/1.29      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.07/1.29        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D)))),
% 1.07/1.29      inference('sup-', [status(thm)], ['8', '9'])).
% 1.07/1.29  thf('11', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.29  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.07/1.29      inference('demod', [status(thm)], ['3', '4'])).
% 1.07/1.29  thf(t16_xboole_1, axiom,
% 1.07/1.29    (![A:$i,B:$i,C:$i]:
% 1.07/1.29     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.07/1.29       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.07/1.29  thf('13', plain,
% 1.07/1.29      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.07/1.29         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.07/1.29           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.07/1.29      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.29  thf('14', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 1.07/1.29           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.07/1.29      inference('sup+', [status(thm)], ['12', '13'])).
% 1.07/1.29  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.07/1.29  thf('15', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 1.07/1.29      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.07/1.29  thf(t28_xboole_1, axiom,
% 1.07/1.29    (![A:$i,B:$i]:
% 1.07/1.29     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.07/1.29  thf('16', plain,
% 1.07/1.29      (![X14 : $i, X15 : $i]:
% 1.07/1.29         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 1.07/1.29      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.07/1.29  thf('17', plain,
% 1.07/1.29      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.07/1.29      inference('sup-', [status(thm)], ['15', '16'])).
% 1.07/1.29  thf('18', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)))),
% 1.07/1.29      inference('demod', [status(thm)], ['14', '17'])).
% 1.07/1.29  thf('19', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.29      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.29  thf('20', plain,
% 1.07/1.29      (![X2 : $i, X4 : $i]:
% 1.07/1.29         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.07/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.29  thf('21', plain,
% 1.07/1.29      (![X0 : $i, X1 : $i]:
% 1.07/1.29         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.07/1.29      inference('sup-', [status(thm)], ['19', '20'])).
% 1.07/1.29  thf('22', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         (((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.29          | (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B))),
% 1.07/1.29      inference('sup-', [status(thm)], ['18', '21'])).
% 1.07/1.29  thf('23', plain,
% 1.07/1.29      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B)),
% 1.07/1.29      inference('simplify', [status(thm)], ['22'])).
% 1.07/1.29  thf('24', plain,
% 1.07/1.29      (![X2 : $i, X3 : $i]:
% 1.07/1.29         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.07/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.29  thf('25', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         ((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ X0) @ sk_B) = (k1_xboole_0))),
% 1.07/1.29      inference('sup-', [status(thm)], ['23', '24'])).
% 1.07/1.29  thf('26', plain,
% 1.07/1.29      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.07/1.29         ((k3_xboole_0 @ (k3_xboole_0 @ X11 @ X12) @ X13)
% 1.07/1.29           = (k3_xboole_0 @ X11 @ (k3_xboole_0 @ X12 @ X13)))),
% 1.07/1.29      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.07/1.29  thf('27', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)) = (k1_xboole_0))),
% 1.07/1.29      inference('demod', [status(thm)], ['25', '26'])).
% 1.07/1.29  thf('28', plain,
% 1.07/1.29      (![X2 : $i, X4 : $i]:
% 1.07/1.29         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.07/1.29      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.29  thf('29', plain,
% 1.07/1.29      (![X0 : $i]:
% 1.07/1.29         (((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.30          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['27', '28'])).
% 1.07/1.30  thf('30', plain,
% 1.07/1.30      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.07/1.30      inference('simplify', [status(thm)], ['29'])).
% 1.07/1.30  thf('31', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(t3_xboole_0, axiom,
% 1.07/1.30    (![A:$i,B:$i]:
% 1.07/1.30     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.07/1.30            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.07/1.30       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.07/1.30            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.07/1.30  thf('32', plain,
% 1.07/1.30      (![X5 : $i, X7 : $i, X8 : $i]:
% 1.07/1.30         (~ (r2_hidden @ X7 @ X5)
% 1.07/1.30          | ~ (r2_hidden @ X7 @ X8)
% 1.07/1.30          | ~ (r1_xboole_0 @ X5 @ X8))),
% 1.07/1.30      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.07/1.30  thf('33', plain,
% 1.07/1.30      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['31', '32'])).
% 1.07/1.30  thf('34', plain,
% 1.07/1.30      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ X0 @ sk_B))),
% 1.07/1.30      inference('sup-', [status(thm)], ['30', '33'])).
% 1.07/1.30  thf('35', plain,
% 1.07/1.30      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k3_xboole_0 @ sk_B @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['11', '34'])).
% 1.07/1.30  thf('36', plain,
% 1.07/1.30      ((~ (r2_hidden @ sk_D @ (k1_tarski @ sk_D))
% 1.07/1.30        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['10', '35'])).
% 1.07/1.30  thf(t69_enumset1, axiom,
% 1.07/1.30    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.07/1.30  thf('37', plain,
% 1.07/1.30      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 1.07/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.07/1.30  thf(t70_enumset1, axiom,
% 1.07/1.30    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.07/1.30  thf('38', plain,
% 1.07/1.30      (![X36 : $i, X37 : $i]:
% 1.07/1.30         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 1.07/1.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.07/1.30  thf(d1_enumset1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.30     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.07/1.30       ( ![E:$i]:
% 1.07/1.30         ( ( r2_hidden @ E @ D ) <=>
% 1.07/1.30           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.07/1.30  thf(zf_stmt_2, axiom,
% 1.07/1.30    (![E:$i,C:$i,B:$i,A:$i]:
% 1.07/1.30     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.07/1.30       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_3, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.30     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.07/1.30       ( ![E:$i]:
% 1.07/1.30         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.07/1.30  thf('39', plain,
% 1.07/1.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.07/1.30         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 1.07/1.30          | (r2_hidden @ X28 @ X32)
% 1.07/1.30          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.07/1.30  thf('40', plain,
% 1.07/1.30      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.07/1.30         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 1.07/1.30          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 1.07/1.30      inference('simplify', [status(thm)], ['39'])).
% 1.07/1.30  thf('41', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.30         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.07/1.30          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.07/1.30      inference('sup+', [status(thm)], ['38', '40'])).
% 1.07/1.30  thf('42', plain,
% 1.07/1.30      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.07/1.30         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.07/1.30  thf('43', plain,
% 1.07/1.30      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.07/1.30         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 1.07/1.30      inference('simplify', [status(thm)], ['42'])).
% 1.07/1.30  thf('44', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.07/1.30      inference('sup-', [status(thm)], ['41', '43'])).
% 1.07/1.30  thf('45', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['37', '44'])).
% 1.07/1.30  thf('46', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.07/1.30      inference('demod', [status(thm)], ['36', '45'])).
% 1.07/1.30  thf('47', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.30  thf(t100_xboole_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]:
% 1.07/1.30     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.07/1.30  thf('48', plain,
% 1.07/1.30      (![X9 : $i, X10 : $i]:
% 1.07/1.30         ((k4_xboole_0 @ X9 @ X10)
% 1.07/1.30           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.07/1.30  thf('49', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         ((k4_xboole_0 @ X0 @ X1)
% 1.07/1.30           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.07/1.30      inference('sup+', [status(thm)], ['47', '48'])).
% 1.07/1.30  thf('50', plain,
% 1.07/1.30      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['46', '49'])).
% 1.07/1.30  thf(t5_boole, axiom,
% 1.07/1.30    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.07/1.30  thf('51', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.07/1.30      inference('cnf', [status(esa)], [t5_boole])).
% 1.07/1.30  thf('52', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.07/1.30      inference('demod', [status(thm)], ['50', '51'])).
% 1.07/1.30  thf(t79_xboole_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.07/1.30  thf('53', plain,
% 1.07/1.30      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 1.07/1.30      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.07/1.30  thf('54', plain,
% 1.07/1.30      (![X2 : $i, X3 : $i]:
% 1.07/1.30         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.07/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.30  thf('55', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['53', '54'])).
% 1.07/1.30  thf('56', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.07/1.30  thf('57', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.07/1.30      inference('demod', [status(thm)], ['55', '56'])).
% 1.07/1.30  thf('58', plain,
% 1.07/1.30      (![X2 : $i, X4 : $i]:
% 1.07/1.30         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.07/1.30      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.07/1.30  thf('59', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.30          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['57', '58'])).
% 1.07/1.30  thf('60', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.07/1.30      inference('simplify', [status(thm)], ['59'])).
% 1.07/1.30  thf(t78_xboole_1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( r1_xboole_0 @ A @ B ) =>
% 1.07/1.30       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.07/1.30         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.07/1.30  thf('61', plain,
% 1.07/1.30      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.07/1.30         (~ (r1_xboole_0 @ X18 @ X19)
% 1.07/1.30          | ((k3_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 1.07/1.30              = (k3_xboole_0 @ X18 @ X20)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.07/1.30  thf('62', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.30         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))
% 1.07/1.30           = (k3_xboole_0 @ X0 @ X2))),
% 1.07/1.30      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.30  thf('63', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 1.07/1.30           = (k3_xboole_0 @ sk_B @ X0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['52', '62'])).
% 1.07/1.30  thf('64', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 1.07/1.30      inference('sup-', [status(thm)], ['19', '20'])).
% 1.07/1.30  thf('65', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.07/1.30          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.07/1.30      inference('sup-', [status(thm)], ['63', '64'])).
% 1.07/1.30  thf('66', plain,
% 1.07/1.30      ((((k1_xboole_0) != (k1_xboole_0))
% 1.07/1.30        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 1.07/1.30      inference('sup-', [status(thm)], ['5', '65'])).
% 1.07/1.30  thf('67', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.07/1.30      inference('simplify', [status(thm)], ['66'])).
% 1.07/1.30  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 1.07/1.30  
% 1.07/1.30  % SZS output end Refutation
% 1.07/1.30  
% 1.17/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
