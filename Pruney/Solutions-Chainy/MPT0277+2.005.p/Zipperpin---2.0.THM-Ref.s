%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YCjLqhy04

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:40 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  165 (1064 expanded)
%              Number of leaves         :   31 ( 305 expanded)
%              Depth                    :   31
%              Number of atoms          : 1519 (12501 expanded)
%              Number of equality atoms :  254 (2325 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t75_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
        = k1_xboole_0 )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) )
          = k1_xboole_0 )
      <=> ~ ( ( A != k1_xboole_0 )
            & ( A
             != ( k1_tarski @ B ) )
            & ( A
             != ( k1_tarski @ C ) )
            & ( A
             != ( k2_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_zfmisc_1])).

thf('1',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A
      = ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('11',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('13',plain,
    ( ( sk_A != sk_A )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['1'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_A )
     != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('47',plain,
    ( ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('53',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A )
      = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('55',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) )
      = ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('57',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('58',plain,
    ( ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,
    ( ( r1_tarski @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('61',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X32
        = ( k2_tarski @ X30 @ X31 ) )
      | ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32
        = ( k1_tarski @ X30 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('62',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('64',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','65'])).

thf('67',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k2_tarski @ sk_B @ sk_C ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['62','66'])).

thf('68',plain,
    ( ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) )
   <= ( sk_A
     != ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['43'])).

thf('69',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_C ) )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( sk_A
        = ( k1_tarski @ sk_B ) )
      | ( sk_A
        = ( k1_tarski @ sk_C ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A
     != ( k1_tarski @ sk_C ) ) ),
    inference(split,[status(esa)],['41'])).

thf('72',plain,
    ( ( ( sk_A != sk_A )
      | ( sk_A
        = ( k1_tarski @ sk_B ) ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
   <= ( sk_A
     != ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['39'])).

thf('75',plain,
    ( ( sk_A != sk_A )
   <= ( ( sk_A
       != ( k2_tarski @ sk_B @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_C ) )
      & ( sk_A
       != ( k1_tarski @ sk_B ) )
      & ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_B ) )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = k1_xboole_0 ) )).

thf('78',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X34 ) @ ( k2_tarski @ X34 @ X35 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t22_zfmisc_1])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ X0 ) )
        = k1_xboole_0 )
   <= ( sk_A
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
       != k1_xboole_0 )
      & ( sk_A
        = ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_A
      = ( k1_tarski @ sk_C ) )
    | ( sk_A
      = ( k1_tarski @ sk_B ) )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = k1_xboole_0 )
    | ( sk_A
      = ( k2_tarski @ sk_B @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('84',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','14','38','40','42','44','76','82','83'])).

thf('85',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','84'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('86',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X32
        = ( k2_tarski @ X30 @ X31 ) )
      | ( X32
        = ( k1_tarski @ X31 ) )
      | ( X32
        = ( k1_tarski @ X30 ) )
      | ( X32 = k1_xboole_0 )
      | ~ ( r1_tarski @ X32 @ ( k2_tarski @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','84'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( X0 = k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_A @ X0 )
        = sk_A )
      | ( ( k4_xboole_0 @ sk_A @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','94'])).

thf('96',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('97',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','42','44','76'])).

thf('98',plain,(
    ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) )
    = sk_A ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_A )
    = ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('104',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('107',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_A @ ( k2_tarski @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['102','109','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('115',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('117',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ sk_A )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['115','116'])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('118',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X40 @ X39 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X38 @ X40 ) @ X39 )
       != ( k2_tarski @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('119',plain,
    ( ( ( k2_tarski @ sk_B @ sk_C )
     != ( k2_tarski @ sk_B @ sk_C ) )
    | ~ ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( r2_hidden @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,
    ( sk_A
    = ( k1_tarski @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['2','84'])).

thf('122',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('123',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('124',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('125',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['123','125'])).

thf('127',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('128',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['122','129'])).

thf('131',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference('sup+',[status(thm)],['121','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['120','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YCjLqhy04
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 14:26:19 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.34  % Running portfolio for 600 s
% 0.15/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 1035 iterations in 0.367s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.61/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.61/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.61/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(t36_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.83  thf('0', plain,
% 0.61/0.83      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.61/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.83  thf(t75_zfmisc_1, conjecture,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.83       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.61/0.83            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.61/0.83        ( ( ( k4_xboole_0 @ A @ ( k2_tarski @ B @ C ) ) = ( k1_xboole_0 ) ) <=>
% 0.61/0.83          ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.61/0.83               ( ( A ) != ( k1_tarski @ C ) ) & 
% 0.61/0.83               ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t75_zfmisc_1])).
% 0.61/0.83  thf('1', plain,
% 0.61/0.83      ((((sk_A) = (k2_tarski @ sk_B @ sk_C))
% 0.61/0.83        | ((sk_A) = (k1_tarski @ sk_C))
% 0.61/0.83        | ((sk_A) = (k1_tarski @ sk_B))
% 0.61/0.83        | ((sk_A) = (k1_xboole_0))
% 0.61/0.83        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('2', plain,
% 0.61/0.83      ((((sk_A) = (k1_tarski @ sk_C))) <= ((((sk_A) = (k1_tarski @ sk_C))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf('3', plain,
% 0.61/0.83      ((((sk_A) != (k1_xboole_0))
% 0.61/0.83        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('4', plain,
% 0.61/0.83      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.61/0.83       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('split', [status(esa)], ['3'])).
% 0.61/0.83  thf('5', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf(t4_boole, axiom,
% 0.61/0.83    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t4_boole])).
% 0.61/0.83  thf('7', plain,
% 0.61/0.83      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))
% 0.61/0.83         <= ((((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.83  thf('8', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf('9', plain,
% 0.61/0.83      ((![X0 : $i]: ((k4_xboole_0 @ sk_A @ X0) = (sk_A)))
% 0.61/0.83         <= ((((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('demod', [status(thm)], ['7', '8'])).
% 0.61/0.83  thf('10', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['3'])).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      ((((sk_A) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.61/0.83             (((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.83  thf('12', plain,
% 0.61/0.83      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf('13', plain,
% 0.61/0.83      ((((sk_A) != (sk_A)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.61/0.83             (((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.83  thf('14', plain,
% 0.61/0.83      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.61/0.83       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['13'])).
% 0.61/0.83  thf(t48_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.83  thf('15', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.61/0.83           = (k3_xboole_0 @ X7 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('16', plain,
% 0.61/0.83      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t4_boole])).
% 0.61/0.83  thf('17', plain,
% 0.61/0.83      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.83  thf('18', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.83  thf(t100_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.83  thf('19', plain,
% 0.61/0.83      (![X2 : $i, X3 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X2 @ X3)
% 0.61/0.83           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.83  thf('20', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.83  thf('21', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['17', '20'])).
% 0.61/0.83  thf('22', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.61/0.83           = (k3_xboole_0 @ X7 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('23', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.61/0.83           = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['21', '22'])).
% 0.61/0.83  thf('24', plain,
% 0.61/0.83      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf('25', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.83  thf('26', plain,
% 0.61/0.83      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['24', '25'])).
% 0.61/0.83  thf('27', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['23', '26'])).
% 0.61/0.83  thf('28', plain,
% 0.61/0.83      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t4_boole])).
% 0.61/0.83  thf(t98_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.61/0.83  thf('29', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         ((k2_xboole_0 @ X10 @ X11)
% 0.61/0.83           = (k5_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.61/0.83  thf('30', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['28', '29'])).
% 0.61/0.83  thf(t1_boole, axiom,
% 0.61/0.83    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.83  thf('31', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.61/0.83      inference('cnf', [status(esa)], [t1_boole])).
% 0.61/0.83  thf('32', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.83  thf('33', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['27', '32'])).
% 0.61/0.83  thf('34', plain,
% 0.61/0.83      ((((sk_A) = (k2_tarski @ sk_B @ sk_C)))
% 0.61/0.83         <= ((((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf('35', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['3'])).
% 0.61/0.83  thf('36', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ sk_A) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.61/0.83             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.83  thf('37', plain,
% 0.61/0.83      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.61/0.83             (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['33', '36'])).
% 0.61/0.83  thf('38', plain,
% 0.61/0.83      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.61/0.83       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['37'])).
% 0.61/0.83  thf('39', plain,
% 0.61/0.83      ((((sk_A) != (k1_tarski @ sk_B))
% 0.61/0.83        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('40', plain,
% 0.61/0.83      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.61/0.83       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('split', [status(esa)], ['39'])).
% 0.61/0.83  thf('41', plain,
% 0.61/0.83      ((((sk_A) != (k1_tarski @ sk_C))
% 0.61/0.83        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('42', plain,
% 0.61/0.83      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.61/0.83       ~ (((sk_A) = (k1_tarski @ sk_C)))),
% 0.61/0.83      inference('split', [status(esa)], ['41'])).
% 0.61/0.83  thf('43', plain,
% 0.61/0.83      ((((sk_A) != (k2_tarski @ sk_B @ sk_C))
% 0.61/0.83        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('44', plain,
% 0.61/0.83      (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | 
% 0.61/0.83       ~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('split', [status(esa)], ['43'])).
% 0.61/0.83  thf('45', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf('46', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.61/0.83           = (k3_xboole_0 @ X7 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('47', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.61/0.83          = (k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['45', '46'])).
% 0.61/0.83  thf('48', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['17', '20'])).
% 0.61/0.83  thf('49', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.83  thf('50', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['48', '49'])).
% 0.61/0.83  thf('51', plain,
% 0.61/0.83      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('demod', [status(thm)], ['47', '50'])).
% 0.61/0.83  thf('52', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.83  thf('53', plain,
% 0.61/0.83      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)
% 0.61/0.83          = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['51', '52'])).
% 0.61/0.83  thf('54', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.61/0.83           = (k3_xboole_0 @ X7 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('55', plain,
% 0.61/0.83      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.61/0.83          (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A))
% 0.61/0.83          = (k3_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['53', '54'])).
% 0.61/0.83  thf('56', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.83  thf('57', plain,
% 0.61/0.83      ((((sk_A) = (k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C))))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('demod', [status(thm)], ['47', '50'])).
% 0.61/0.83  thf('58', plain,
% 0.61/0.83      ((((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ 
% 0.61/0.83          (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)) = (sk_A)))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.61/0.83  thf('59', plain,
% 0.61/0.83      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.61/0.83      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.61/0.83  thf('60', plain,
% 0.61/0.83      (((r1_tarski @ sk_A @ (k2_tarski @ sk_B @ sk_C)))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['58', '59'])).
% 0.61/0.83  thf(l45_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.61/0.83       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.61/0.83            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.61/0.83  thf('61', plain,
% 0.61/0.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.83         (((X32) = (k2_tarski @ X30 @ X31))
% 0.61/0.83          | ((X32) = (k1_tarski @ X31))
% 0.61/0.83          | ((X32) = (k1_tarski @ X30))
% 0.61/0.83          | ((X32) = (k1_xboole_0))
% 0.61/0.83          | ~ (r1_tarski @ X32 @ (k2_tarski @ X30 @ X31)))),
% 0.61/0.83      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.61/0.83  thf('62', plain,
% 0.61/0.83      (((((sk_A) = (k1_xboole_0))
% 0.61/0.83         | ((sk_A) = (k1_tarski @ sk_B))
% 0.61/0.83         | ((sk_A) = (k1_tarski @ sk_C))
% 0.61/0.83         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['60', '61'])).
% 0.61/0.83  thf('63', plain,
% 0.61/0.83      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['3'])).
% 0.61/0.83  thf('64', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.61/0.83       ~ (((sk_A) = (k1_xboole_0)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['13'])).
% 0.61/0.83  thf('65', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['4', '64'])).
% 0.61/0.83  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['63', '65'])).
% 0.61/0.83  thf('67', plain,
% 0.61/0.83      (((((sk_A) = (k1_tarski @ sk_B))
% 0.61/0.83         | ((sk_A) = (k1_tarski @ sk_C))
% 0.61/0.83         | ((sk_A) = (k2_tarski @ sk_B @ sk_C))))
% 0.61/0.83         <= ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['62', '66'])).
% 0.61/0.83  thf('68', plain,
% 0.61/0.83      ((((sk_A) != (k2_tarski @ sk_B @ sk_C)))
% 0.61/0.83         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))))),
% 0.61/0.83      inference('split', [status(esa)], ['43'])).
% 0.61/0.83  thf('69', plain,
% 0.61/0.83      (((((sk_A) != (sk_A))
% 0.61/0.83         | ((sk_A) = (k1_tarski @ sk_C))
% 0.61/0.83         | ((sk_A) = (k1_tarski @ sk_B))))
% 0.61/0.83         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['67', '68'])).
% 0.61/0.83  thf('70', plain,
% 0.61/0.83      (((((sk_A) = (k1_tarski @ sk_B)) | ((sk_A) = (k1_tarski @ sk_C))))
% 0.61/0.83         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('simplify', [status(thm)], ['69'])).
% 0.61/0.83  thf('71', plain,
% 0.61/0.83      ((((sk_A) != (k1_tarski @ sk_C))) <= (~ (((sk_A) = (k1_tarski @ sk_C))))),
% 0.61/0.83      inference('split', [status(esa)], ['41'])).
% 0.61/0.83  thf('72', plain,
% 0.61/0.83      (((((sk_A) != (sk_A)) | ((sk_A) = (k1_tarski @ sk_B))))
% 0.61/0.83         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.61/0.83             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['70', '71'])).
% 0.61/0.83  thf('73', plain,
% 0.61/0.83      ((((sk_A) = (k1_tarski @ sk_B)))
% 0.61/0.83         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.61/0.83             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('simplify', [status(thm)], ['72'])).
% 0.61/0.83  thf('74', plain,
% 0.61/0.83      ((((sk_A) != (k1_tarski @ sk_B))) <= (~ (((sk_A) = (k1_tarski @ sk_B))))),
% 0.61/0.83      inference('split', [status(esa)], ['39'])).
% 0.61/0.83  thf('75', plain,
% 0.61/0.83      ((((sk_A) != (sk_A)))
% 0.61/0.83         <= (~ (((sk_A) = (k2_tarski @ sk_B @ sk_C))) & 
% 0.61/0.83             ~ (((sk_A) = (k1_tarski @ sk_C))) & 
% 0.61/0.83             ~ (((sk_A) = (k1_tarski @ sk_B))) & 
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['73', '74'])).
% 0.61/0.83  thf('76', plain,
% 0.61/0.83      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.61/0.83       (((sk_A) = (k1_tarski @ sk_B))) | (((sk_A) = (k1_tarski @ sk_C))) | 
% 0.61/0.83       (((sk_A) = (k2_tarski @ sk_B @ sk_C)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['75'])).
% 0.61/0.83  thf('77', plain,
% 0.61/0.83      ((((sk_A) = (k1_tarski @ sk_B))) <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf(t22_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.61/0.83       ( k1_xboole_0 ) ))).
% 0.61/0.83  thf('78', plain,
% 0.61/0.83      (![X34 : $i, X35 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ (k1_tarski @ X34) @ (k2_tarski @ X34 @ X35))
% 0.61/0.83           = (k1_xboole_0))),
% 0.61/0.83      inference('cnf', [status(esa)], [t22_zfmisc_1])).
% 0.61/0.83  thf('79', plain,
% 0.61/0.83      ((![X0 : $i]:
% 0.61/0.83          ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ X0)) = (k1_xboole_0)))
% 0.61/0.83         <= ((((sk_A) = (k1_tarski @ sk_B))))),
% 0.61/0.83      inference('sup+', [status(thm)], ['77', '78'])).
% 0.61/0.83  thf('80', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['3'])).
% 0.61/0.83  thf('81', plain,
% 0.61/0.83      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) & 
% 0.61/0.83             (((sk_A) = (k1_tarski @ sk_B))))),
% 0.61/0.83      inference('sup-', [status(thm)], ['79', '80'])).
% 0.61/0.83  thf('82', plain,
% 0.61/0.83      (~ (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.61/0.83       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['81'])).
% 0.61/0.83  thf('83', plain,
% 0.61/0.83      ((((sk_A) = (k1_tarski @ sk_C))) | (((sk_A) = (k1_tarski @ sk_B))) | 
% 0.61/0.83       (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))) | 
% 0.61/0.83       (((sk_A) = (k2_tarski @ sk_B @ sk_C))) | (((sk_A) = (k1_xboole_0)))),
% 0.61/0.83      inference('split', [status(esa)], ['1'])).
% 0.61/0.83  thf('84', plain, ((((sk_A) = (k1_tarski @ sk_C)))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)],
% 0.61/0.83                ['4', '14', '38', '40', '42', '44', '76', '82', '83'])).
% 0.61/0.83  thf('85', plain, (((sk_A) = (k1_tarski @ sk_C))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['2', '84'])).
% 0.61/0.83  thf(t69_enumset1, axiom,
% 0.61/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.83  thf('86', plain,
% 0.61/0.83      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.61/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.83  thf('87', plain,
% 0.61/0.83      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.61/0.83         (((X32) = (k2_tarski @ X30 @ X31))
% 0.61/0.83          | ((X32) = (k1_tarski @ X31))
% 0.61/0.83          | ((X32) = (k1_tarski @ X30))
% 0.61/0.83          | ((X32) = (k1_xboole_0))
% 0.61/0.83          | ~ (r1_tarski @ X32 @ (k2_tarski @ X30 @ X31)))),
% 0.61/0.83      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.61/0.83  thf('88', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k1_xboole_0))
% 0.61/0.83          | ((X1) = (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['86', '87'])).
% 0.61/0.83  thf('89', plain,
% 0.61/0.83      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.61/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.83  thf('90', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k1_xboole_0))
% 0.61/0.83          | ((X1) = (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k1_tarski @ X0)))),
% 0.61/0.83      inference('demod', [status(thm)], ['88', '89'])).
% 0.61/0.83  thf('91', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (((X1) = (k1_tarski @ X0))
% 0.61/0.83          | ((X1) = (k1_xboole_0))
% 0.61/0.83          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['90'])).
% 0.61/0.83  thf('92', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r1_tarski @ X0 @ sk_A)
% 0.61/0.83          | ((X0) = (k1_xboole_0))
% 0.61/0.83          | ((X0) = (k1_tarski @ sk_C)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['85', '91'])).
% 0.61/0.83  thf('93', plain, (((sk_A) = (k1_tarski @ sk_C))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['2', '84'])).
% 0.61/0.83  thf('94', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r1_tarski @ X0 @ sk_A) | ((X0) = (k1_xboole_0)) | ((X0) = (sk_A)))),
% 0.61/0.83      inference('demod', [status(thm)], ['92', '93'])).
% 0.61/0.83  thf('95', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (((k4_xboole_0 @ sk_A @ X0) = (sk_A))
% 0.61/0.83          | ((k4_xboole_0 @ sk_A @ X0) = (k1_xboole_0)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['0', '94'])).
% 0.61/0.83  thf('96', plain,
% 0.61/0.83      ((((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0)))
% 0.61/0.83         <= (~
% 0.61/0.83             (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0))))),
% 0.61/0.83      inference('split', [status(esa)], ['3'])).
% 0.61/0.83  thf('97', plain,
% 0.61/0.83      (~ (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (k1_xboole_0)))),
% 0.61/0.83      inference('sat_resolution*', [status(thm)], ['40', '42', '44', '76'])).
% 0.61/0.83  thf('98', plain,
% 0.61/0.83      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) != (k1_xboole_0))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['96', '97'])).
% 0.61/0.83  thf('99', plain,
% 0.61/0.83      ((((k1_xboole_0) != (k1_xboole_0))
% 0.61/0.83        | ((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (sk_A)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['95', '98'])).
% 0.61/0.83  thf('100', plain,
% 0.61/0.83      (((k4_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)) = (sk_A))),
% 0.61/0.83      inference('simplify', [status(thm)], ['99'])).
% 0.61/0.83  thf('101', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.61/0.83           = (k3_xboole_0 @ X7 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('102', plain,
% 0.61/0.83      (((k4_xboole_0 @ sk_A @ sk_A)
% 0.61/0.83         = (k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['100', '101'])).
% 0.61/0.83  thf('103', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['27', '32'])).
% 0.61/0.83  thf('104', plain,
% 0.61/0.83      (![X7 : $i, X8 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 0.61/0.83           = (k3_xboole_0 @ X7 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('105', plain,
% 0.61/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['103', '104'])).
% 0.61/0.83  thf('106', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['48', '49'])).
% 0.61/0.83  thf('107', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['105', '106'])).
% 0.61/0.83  thf('108', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.83  thf('109', plain,
% 0.61/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['107', '108'])).
% 0.61/0.83  thf('110', plain,
% 0.61/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['107', '108'])).
% 0.61/0.83  thf('111', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['27', '32'])).
% 0.61/0.83  thf('112', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['110', '111'])).
% 0.61/0.83  thf('113', plain,
% 0.61/0.83      (((k1_xboole_0) = (k3_xboole_0 @ sk_A @ (k2_tarski @ sk_B @ sk_C)))),
% 0.61/0.83      inference('demod', [status(thm)], ['102', '109', '112'])).
% 0.61/0.83  thf('114', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ X1)
% 0.61/0.83           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['18', '19'])).
% 0.61/0.83  thf('115', plain,
% 0.61/0.83      (((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)
% 0.61/0.83         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['113', '114'])).
% 0.61/0.83  thf('116', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['30', '31'])).
% 0.61/0.83  thf('117', plain,
% 0.61/0.83      (((k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ sk_A)
% 0.61/0.83         = (k2_tarski @ sk_B @ sk_C))),
% 0.61/0.83      inference('demod', [status(thm)], ['115', '116'])).
% 0.61/0.83  thf(t72_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.61/0.83       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.61/0.83  thf('118', plain,
% 0.61/0.83      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X40 @ X39)
% 0.61/0.83          | ((k4_xboole_0 @ (k2_tarski @ X38 @ X40) @ X39)
% 0.61/0.83              != (k2_tarski @ X38 @ X40)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.61/0.83  thf('119', plain,
% 0.61/0.83      ((((k2_tarski @ sk_B @ sk_C) != (k2_tarski @ sk_B @ sk_C))
% 0.61/0.83        | ~ (r2_hidden @ sk_C @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['117', '118'])).
% 0.61/0.83  thf('120', plain, (~ (r2_hidden @ sk_C @ sk_A)),
% 0.61/0.83      inference('simplify', [status(thm)], ['119'])).
% 0.61/0.83  thf('121', plain, (((sk_A) = (k1_tarski @ sk_C))),
% 0.61/0.83      inference('simpl_trail', [status(thm)], ['2', '84'])).
% 0.61/0.83  thf('122', plain,
% 0.61/0.83      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.61/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.83  thf(t70_enumset1, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.61/0.83  thf('123', plain,
% 0.61/0.83      (![X25 : $i, X26 : $i]:
% 0.61/0.83         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.61/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.83  thf(d1_enumset1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.61/0.83       ( ![E:$i]:
% 0.61/0.83         ( ( r2_hidden @ E @ D ) <=>
% 0.61/0.83           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.61/0.83  thf(zf_stmt_2, axiom,
% 0.61/0.83    (![E:$i,C:$i,B:$i,A:$i]:
% 0.61/0.83     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.61/0.83       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_3, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.61/0.83       ( ![E:$i]:
% 0.61/0.83         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.61/0.83  thf('124', plain,
% 0.61/0.83      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.61/0.83         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.61/0.83          | (r2_hidden @ X17 @ X21)
% 0.61/0.83          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.83  thf('125', plain,
% 0.61/0.83      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.61/0.83         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.61/0.83          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.61/0.83      inference('simplify', [status(thm)], ['124'])).
% 0.61/0.83  thf('126', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.83         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.61/0.83          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.61/0.83      inference('sup+', [status(thm)], ['123', '125'])).
% 0.61/0.83  thf('127', plain,
% 0.61/0.83      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.61/0.83         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.83  thf('128', plain,
% 0.61/0.83      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.61/0.83         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X12)),
% 0.61/0.83      inference('simplify', [status(thm)], ['127'])).
% 0.61/0.83  thf('129', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['126', '128'])).
% 0.61/0.83  thf('130', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['122', '129'])).
% 0.61/0.83  thf('131', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.61/0.83      inference('sup+', [status(thm)], ['121', '130'])).
% 0.61/0.83  thf('132', plain, ($false), inference('demod', [status(thm)], ['120', '131'])).
% 0.61/0.83  
% 0.61/0.83  % SZS output end Refutation
% 0.61/0.83  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
