%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wQVWahvTZp

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:37 EST 2020

% Result     : Theorem 13.73s
% Output     : Refutation 13.73s
% Verified   : 
% Statistics : Number of formulae       :  204 (1136 expanded)
%              Number of leaves         :   36 ( 327 expanded)
%              Depth                    :   31
%              Number of atoms          : 1625 (11351 expanded)
%              Number of equality atoms :  254 (1883 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X68: $i,X70: $i,X71: $i] :
      ( ( r1_tarski @ X70 @ ( k2_tarski @ X68 @ X71 ) )
      | ( X70
       != ( k1_tarski @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('2',plain,(
    ! [X68: $i,X71: $i] :
      ( r1_tarski @ ( k1_tarski @ X71 ) @ ( k2_tarski @ X68 @ X71 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','27'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('30',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k2_tarski @ X36 @ X37 ) @ ( k2_tarski @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('37',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( k2_enumset1 @ X43 @ X43 @ X44 @ X45 )
      = ( k1_enumset1 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('38',plain,
    ( ( k1_enumset1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['33','36','37'])).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r2_hidden @ sk_B @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('45',plain,(
    ! [X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X32 )
      | ( X34 = X33 )
      | ( X34 = X30 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('46',plain,(
    ! [X30: $i,X33: $i,X34: $i] :
      ( ( X34 = X30 )
      | ( X34 = X33 )
      | ~ ( r2_hidden @ X34 @ ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_B = sk_C )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( X70
        = ( k2_tarski @ X68 @ X69 ) )
      | ( X70
        = ( k1_tarski @ X69 ) )
      | ( X70
        = ( k1_tarski @ X68 ) )
      | ( X70 = k1_xboole_0 )
      | ~ ( r1_tarski @ X70 @ ( k2_tarski @ X68 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('50',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X31 != X30 )
      | ( r2_hidden @ X31 @ X32 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('52',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X30: $i,X33: $i,X34: $i] :
      ( ( X34 = X30 )
      | ( X34 = X33 )
      | ~ ( r2_hidden @ X34 @ ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('55',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_A )
    | ( sk_D_1 = sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('59',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('61',plain,(
    ! [X30: $i,X33: $i,X34: $i] :
      ( ( X34 = X30 )
      | ( X34 = X33 )
      | ~ ( r2_hidden @ X34 @ ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_B )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( X31 != X33 )
      | ( r2_hidden @ X31 @ X32 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('67',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X33 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['65','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('70',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X33 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('74',plain,
    ( ( r2_hidden @ sk_A @ k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('76',plain,(
    ! [X68: $i,X71: $i] :
      ( r1_tarski @ ( k1_tarski @ X71 ) @ ( k2_tarski @ X68 @ X71 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('77',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( sk_D_1 = sk_B ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('79',plain,
    ( ( sk_D_1 = sk_B )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('81',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_D_1 = sk_B )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( sk_D_1 = sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_D_1 = sk_B )
    | ( sk_A = sk_B )
    | ( sk_D_1 = sk_B ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,
    ( ( sk_A = sk_B )
    | ( sk_D_1 = sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X33 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('90',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('91',plain,(
    ! [X30: $i,X33: $i,X34: $i] :
      ( ( X34 = X30 )
      | ( X34 = X33 )
      | ~ ( r2_hidden @ X34 @ ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_D_1 ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = ( k1_tarski @ sk_C ) )
      | ( ( k2_tarski @ sk_A @ sk_B )
        = k1_xboole_0 )
      | ( X0 = sk_C )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X33 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('98',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('100',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_A = sk_D_1 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('104',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('106',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('108',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( sk_B = sk_C ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X68: $i,X70: $i,X71: $i] :
      ( ( r1_tarski @ X70 @ ( k2_tarski @ X68 @ X71 ) )
      | ( X70
       != ( k1_tarski @ X68 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('110',plain,(
    ! [X68: $i,X71: $i] :
      ( r1_tarski @ ( k1_tarski @ X68 ) @ ( k2_tarski @ X68 @ X71 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('112',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( X70
        = ( k2_tarski @ X68 @ X69 ) )
      | ( X70
        = ( k1_tarski @ X69 ) )
      | ( X70
        = ( k1_tarski @ X68 ) )
      | ( X70 = k1_xboole_0 )
      | ~ ( r1_tarski @ X70 @ ( k2_tarski @ X68 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('114',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('116',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('118',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) )
    | ( sk_D_1 = sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('122',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X30 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('126',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D_1 = sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = ( k1_tarski @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('130',plain,
    ( ( r2_hidden @ sk_C @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('132',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( sk_B = sk_C )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['108','136'])).

thf('138',plain,
    ( ( sk_D_1 = sk_C )
    | ( sk_A = sk_B )
    | ( sk_B = sk_A ) ),
    inference('sup+',[status(thm)],['88','137'])).

thf('139',plain,
    ( ( sk_A = sk_B )
    | ( sk_D_1 = sk_C ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_B = sk_C )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['47','139'])).

thf('141',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( sk_B = sk_C )
    | ( sk_D_1 = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( sk_B = sk_C )
    | ( sk_B = sk_D_1 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('144',plain,
    ( ( sk_D_1 != sk_C )
    | ( sk_B = sk_C ) ),
    inference(eq_fact,[status(thm)],['143'])).

thf('145',plain,(
    sk_B = sk_C ),
    inference(clc,[status(thm)],['142','144'])).

thf('146',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','145'])).

thf('147',plain,
    ( ( sk_A = sk_B )
    | ( sk_D_1 = sk_C ) ),
    inference(simplify,[status(thm)],['138'])).

thf('148',plain,(
    sk_B = sk_C ),
    inference(clc,[status(thm)],['142','144'])).

thf('149',plain,
    ( ( sk_A = sk_C )
    | ( sk_D_1 = sk_C ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    sk_D_1 = sk_C ),
    inference('simplify_reflect-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('153',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_C ) @ ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['146','151','152'])).

thf('154',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('155',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k1_tarski @ sk_C ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('157',plain,(
    ! [X68: $i,X71: $i] :
      ( r1_tarski @ ( k1_tarski @ X71 ) @ ( k2_tarski @ X68 @ X71 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('158',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k1_tarski @ sk_C )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['155','156','159'])).

thf('161',plain,(
    ! [X30: $i,X33: $i] :
      ( r2_hidden @ X33 @ ( k2_tarski @ X33 @ X30 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('162',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('164',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['164','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wQVWahvTZp
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:40:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.73/13.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 13.73/13.91  % Solved by: fo/fo7.sh
% 13.73/13.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.73/13.91  % done 14575 iterations in 13.456s
% 13.73/13.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 13.73/13.91  % SZS output start Refutation
% 13.73/13.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.73/13.91  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 13.73/13.91  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 13.73/13.91  thf(sk_B_type, type, sk_B: $i).
% 13.73/13.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 13.73/13.91  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 13.73/13.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 13.73/13.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.73/13.91  thf(sk_C_type, type, sk_C: $i).
% 13.73/13.91  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.73/13.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.73/13.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.73/13.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.73/13.91  thf(sk_A_type, type, sk_A: $i).
% 13.73/13.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.73/13.91  thf(sk_D_1_type, type, sk_D_1: $i).
% 13.73/13.91  thf(t28_zfmisc_1, conjecture,
% 13.73/13.91    (![A:$i,B:$i,C:$i,D:$i]:
% 13.73/13.91     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 13.73/13.91          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 13.73/13.91  thf(zf_stmt_0, negated_conjecture,
% 13.73/13.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 13.73/13.91        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 13.73/13.91             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 13.73/13.91    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 13.73/13.91  thf('0', plain,
% 13.73/13.91      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf(l45_zfmisc_1, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i]:
% 13.73/13.91     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 13.73/13.91       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 13.73/13.91            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 13.73/13.91  thf('1', plain,
% 13.73/13.91      (![X68 : $i, X70 : $i, X71 : $i]:
% 13.73/13.91         ((r1_tarski @ X70 @ (k2_tarski @ X68 @ X71))
% 13.73/13.91          | ((X70) != (k1_tarski @ X71)))),
% 13.73/13.91      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 13.73/13.91  thf('2', plain,
% 13.73/13.91      (![X68 : $i, X71 : $i]:
% 13.73/13.91         (r1_tarski @ (k1_tarski @ X71) @ (k2_tarski @ X68 @ X71))),
% 13.73/13.91      inference('simplify', [status(thm)], ['1'])).
% 13.73/13.91  thf('3', plain,
% 13.73/13.91      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf(t28_xboole_1, axiom,
% 13.73/13.91    (![A:$i,B:$i]:
% 13.73/13.91     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 13.73/13.91  thf('4', plain,
% 13.73/13.91      (![X10 : $i, X11 : $i]:
% 13.73/13.91         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 13.73/13.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.73/13.91  thf('5', plain,
% 13.73/13.91      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 13.73/13.91         = (k2_tarski @ sk_A @ sk_B))),
% 13.73/13.91      inference('sup-', [status(thm)], ['3', '4'])).
% 13.73/13.91  thf(commutativity_k3_xboole_0, axiom,
% 13.73/13.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 13.73/13.91  thf('6', plain,
% 13.73/13.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 13.73/13.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 13.73/13.91  thf(t18_xboole_1, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i]:
% 13.73/13.91     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 13.73/13.91  thf('7', plain,
% 13.73/13.91      (![X7 : $i, X8 : $i, X9 : $i]:
% 13.73/13.91         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 13.73/13.91      inference('cnf', [status(esa)], [t18_xboole_1])).
% 13.73/13.91  thf('8', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.91         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 13.73/13.91      inference('sup-', [status(thm)], ['6', '7'])).
% 13.73/13.91  thf('9', plain,
% 13.73/13.91      (![X0 : $i]:
% 13.73/13.91         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 13.73/13.91          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['5', '8'])).
% 13.73/13.91  thf('10', plain,
% 13.73/13.91      ((r1_tarski @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('sup-', [status(thm)], ['2', '9'])).
% 13.73/13.91  thf('11', plain,
% 13.73/13.91      (![X10 : $i, X11 : $i]:
% 13.73/13.91         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 13.73/13.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.73/13.91  thf('12', plain,
% 13.73/13.91      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 13.73/13.91         = (k1_tarski @ sk_B))),
% 13.73/13.91      inference('sup-', [status(thm)], ['10', '11'])).
% 13.73/13.91  thf(t100_xboole_1, axiom,
% 13.73/13.91    (![A:$i,B:$i]:
% 13.73/13.91     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 13.73/13.91  thf('13', plain,
% 13.73/13.91      (![X5 : $i, X6 : $i]:
% 13.73/13.91         ((k4_xboole_0 @ X5 @ X6)
% 13.73/13.91           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 13.73/13.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 13.73/13.91  thf('14', plain,
% 13.73/13.91      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 13.73/13.91         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['12', '13'])).
% 13.73/13.91  thf(idempotence_k3_xboole_0, axiom,
% 13.73/13.91    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 13.73/13.91  thf('15', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 13.73/13.91      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 13.73/13.91  thf('16', plain,
% 13.73/13.91      (![X5 : $i, X6 : $i]:
% 13.73/13.91         ((k4_xboole_0 @ X5 @ X6)
% 13.73/13.91           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 13.73/13.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 13.73/13.91  thf('17', plain,
% 13.73/13.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['15', '16'])).
% 13.73/13.91  thf(t2_boole, axiom,
% 13.73/13.91    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 13.73/13.91  thf('18', plain,
% 13.73/13.91      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 13.73/13.91      inference('cnf', [status(esa)], [t2_boole])).
% 13.73/13.91  thf('19', plain,
% 13.73/13.91      (![X5 : $i, X6 : $i]:
% 13.73/13.91         ((k4_xboole_0 @ X5 @ X6)
% 13.73/13.91           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 13.73/13.91      inference('cnf', [status(esa)], [t100_xboole_1])).
% 13.73/13.91  thf('20', plain,
% 13.73/13.91      (![X0 : $i]:
% 13.73/13.91         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['18', '19'])).
% 13.73/13.91  thf(t5_boole, axiom,
% 13.73/13.91    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 13.73/13.91  thf('21', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 13.73/13.91      inference('cnf', [status(esa)], [t5_boole])).
% 13.73/13.91  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 13.73/13.91      inference('demod', [status(thm)], ['20', '21'])).
% 13.73/13.91  thf(t48_xboole_1, axiom,
% 13.73/13.91    (![A:$i,B:$i]:
% 13.73/13.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 13.73/13.91  thf('23', plain,
% 13.73/13.91      (![X13 : $i, X14 : $i]:
% 13.73/13.91         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 13.73/13.91           = (k3_xboole_0 @ X13 @ X14))),
% 13.73/13.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 13.73/13.91  thf('24', plain,
% 13.73/13.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['22', '23'])).
% 13.73/13.91  thf('25', plain,
% 13.73/13.91      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 13.73/13.91      inference('cnf', [status(esa)], [t2_boole])).
% 13.73/13.91  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 13.73/13.91      inference('demod', [status(thm)], ['24', '25'])).
% 13.73/13.91  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['17', '26'])).
% 13.73/13.91  thf('28', plain,
% 13.73/13.91      (((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 13.73/13.91         = (k1_xboole_0))),
% 13.73/13.91      inference('demod', [status(thm)], ['14', '27'])).
% 13.73/13.91  thf(t98_xboole_1, axiom,
% 13.73/13.91    (![A:$i,B:$i]:
% 13.73/13.91     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 13.73/13.91  thf('29', plain,
% 13.73/13.91      (![X16 : $i, X17 : $i]:
% 13.73/13.91         ((k2_xboole_0 @ X16 @ X17)
% 13.73/13.91           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 13.73/13.91      inference('cnf', [status(esa)], [t98_xboole_1])).
% 13.73/13.91  thf('30', plain,
% 13.73/13.91      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ (k1_tarski @ sk_B))
% 13.73/13.91         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ k1_xboole_0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['28', '29'])).
% 13.73/13.91  thf(commutativity_k2_xboole_0, axiom,
% 13.73/13.91    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 13.73/13.91  thf('31', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 13.73/13.91      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 13.73/13.91  thf('32', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 13.73/13.91      inference('cnf', [status(esa)], [t5_boole])).
% 13.73/13.91  thf('33', plain,
% 13.73/13.91      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 13.73/13.91         = (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('demod', [status(thm)], ['30', '31', '32'])).
% 13.73/13.91  thf(t69_enumset1, axiom,
% 13.73/13.91    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 13.73/13.91  thf('34', plain,
% 13.73/13.91      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 13.73/13.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 13.73/13.91  thf(l53_enumset1, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i,D:$i]:
% 13.73/13.91     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 13.73/13.91       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 13.73/13.91  thf('35', plain,
% 13.73/13.91      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 13.73/13.91         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 13.73/13.91           = (k2_xboole_0 @ (k2_tarski @ X36 @ X37) @ (k2_tarski @ X38 @ X39)))),
% 13.73/13.91      inference('cnf', [status(esa)], [l53_enumset1])).
% 13.73/13.91  thf('36', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.73/13.91         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 13.73/13.91           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['34', '35'])).
% 13.73/13.91  thf(t71_enumset1, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i]:
% 13.73/13.91     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 13.73/13.91  thf('37', plain,
% 13.73/13.91      (![X43 : $i, X44 : $i, X45 : $i]:
% 13.73/13.91         ((k2_enumset1 @ X43 @ X43 @ X44 @ X45)
% 13.73/13.91           = (k1_enumset1 @ X43 @ X44 @ X45))),
% 13.73/13.91      inference('cnf', [status(esa)], [t71_enumset1])).
% 13.73/13.91  thf('38', plain,
% 13.73/13.91      (((k1_enumset1 @ sk_B @ sk_C @ sk_D_1) = (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('demod', [status(thm)], ['33', '36', '37'])).
% 13.73/13.91  thf(d1_enumset1, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i,D:$i]:
% 13.73/13.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 13.73/13.91       ( ![E:$i]:
% 13.73/13.91         ( ( r2_hidden @ E @ D ) <=>
% 13.73/13.91           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 13.73/13.91  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 13.73/13.91  thf(zf_stmt_2, axiom,
% 13.73/13.91    (![E:$i,C:$i,B:$i,A:$i]:
% 13.73/13.91     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 13.73/13.91       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 13.73/13.91  thf(zf_stmt_3, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i,D:$i]:
% 13.73/13.91     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 13.73/13.91       ( ![E:$i]:
% 13.73/13.91         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 13.73/13.91  thf('39', plain,
% 13.73/13.91      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 13.73/13.91         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 13.73/13.91          | (r2_hidden @ X23 @ X27)
% 13.73/13.91          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 13.73/13.91  thf('40', plain,
% 13.73/13.91      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 13.73/13.91         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 13.73/13.91          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 13.73/13.91      inference('simplify', [status(thm)], ['39'])).
% 13.73/13.91  thf('41', plain,
% 13.73/13.91      (![X0 : $i]:
% 13.73/13.91         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D_1))
% 13.73/13.91          | (zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_B))),
% 13.73/13.91      inference('sup+', [status(thm)], ['38', '40'])).
% 13.73/13.91  thf('42', plain,
% 13.73/13.91      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 13.73/13.91         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_2])).
% 13.73/13.91  thf('43', plain,
% 13.73/13.91      (![X18 : $i, X20 : $i, X21 : $i]:
% 13.73/13.91         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 13.73/13.91      inference('simplify', [status(thm)], ['42'])).
% 13.73/13.91  thf('44', plain, ((r2_hidden @ sk_B @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('sup-', [status(thm)], ['41', '43'])).
% 13.73/13.91  thf(d2_tarski, axiom,
% 13.73/13.91    (![A:$i,B:$i,C:$i]:
% 13.73/13.91     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 13.73/13.91       ( ![D:$i]:
% 13.73/13.91         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 13.73/13.91  thf('45', plain,
% 13.73/13.91      (![X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 13.73/13.91         (~ (r2_hidden @ X34 @ X32)
% 13.73/13.91          | ((X34) = (X33))
% 13.73/13.91          | ((X34) = (X30))
% 13.73/13.91          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('cnf', [status(esa)], [d2_tarski])).
% 13.73/13.91  thf('46', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i, X34 : $i]:
% 13.73/13.91         (((X34) = (X30))
% 13.73/13.91          | ((X34) = (X33))
% 13.73/13.91          | ~ (r2_hidden @ X34 @ (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['45'])).
% 13.73/13.91  thf('47', plain, ((((sk_B) = (sk_C)) | ((sk_B) = (sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['44', '46'])).
% 13.73/13.91  thf('48', plain,
% 13.73/13.91      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('49', plain,
% 13.73/13.91      (![X68 : $i, X69 : $i, X70 : $i]:
% 13.73/13.91         (((X70) = (k2_tarski @ X68 @ X69))
% 13.73/13.91          | ((X70) = (k1_tarski @ X69))
% 13.73/13.91          | ((X70) = (k1_tarski @ X68))
% 13.73/13.91          | ((X70) = (k1_xboole_0))
% 13.73/13.91          | ~ (r1_tarski @ X70 @ (k2_tarski @ X68 @ X69)))),
% 13.73/13.91      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 13.73/13.91  thf('50', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['48', '49'])).
% 13.73/13.91  thf('51', plain,
% 13.73/13.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 13.73/13.91         (((X31) != (X30))
% 13.73/13.91          | (r2_hidden @ X31 @ X32)
% 13.73/13.91          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('cnf', [status(esa)], [d2_tarski])).
% 13.73/13.91  thf('52', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['51'])).
% 13.73/13.91  thf('53', plain,
% 13.73/13.91      (((r2_hidden @ sk_D_1 @ (k2_tarski @ sk_A @ sk_B))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['50', '52'])).
% 13.73/13.91  thf('54', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i, X34 : $i]:
% 13.73/13.91         (((X34) = (X30))
% 13.73/13.91          | ((X34) = (X33))
% 13.73/13.91          | ~ (r2_hidden @ X34 @ (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['45'])).
% 13.73/13.91  thf('55', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((sk_D_1) = (sk_A))
% 13.73/13.91        | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['53', '54'])).
% 13.73/13.91  thf('56', plain, (((sk_A) != (sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('57', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['55', '56'])).
% 13.73/13.91  thf('58', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['51'])).
% 13.73/13.91  thf('59', plain,
% 13.73/13.91      (((r2_hidden @ sk_B @ (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((sk_D_1) = (sk_B))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['57', '58'])).
% 13.73/13.91  thf('60', plain,
% 13.73/13.91      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 13.73/13.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 13.73/13.91  thf('61', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i, X34 : $i]:
% 13.73/13.91         (((X34) = (X30))
% 13.73/13.91          | ((X34) = (X33))
% 13.73/13.91          | ~ (r2_hidden @ X34 @ (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['45'])).
% 13.73/13.91  thf('62', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['60', '61'])).
% 13.73/13.91  thf('63', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('64', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((sk_D_1) = (sk_B))
% 13.73/13.91        | ((sk_B) = (sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['59', '63'])).
% 13.73/13.91  thf('65', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['64'])).
% 13.73/13.91  thf('66', plain,
% 13.73/13.91      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 13.73/13.91         (((X31) != (X33))
% 13.73/13.91          | (r2_hidden @ X31 @ X32)
% 13.73/13.91          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('cnf', [status(esa)], [d2_tarski])).
% 13.73/13.91  thf('67', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X33 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['66'])).
% 13.73/13.91  thf('68', plain,
% 13.73/13.91      (((r2_hidden @ sk_A @ (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['65', '67'])).
% 13.73/13.91  thf('69', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('70', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((sk_A) = (sk_C)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['68', '69'])).
% 13.73/13.91  thf('71', plain, (((sk_A) != (sk_C))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('72', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B)) | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 13.73/13.91  thf('73', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X33 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['66'])).
% 13.73/13.91  thf('74', plain, (((r2_hidden @ sk_A @ k1_xboole_0) | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['72', '73'])).
% 13.73/13.91  thf('75', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B)) | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 13.73/13.91  thf('76', plain,
% 13.73/13.91      (![X68 : $i, X71 : $i]:
% 13.73/13.91         (r1_tarski @ (k1_tarski @ X71) @ (k2_tarski @ X68 @ X71))),
% 13.73/13.91      inference('simplify', [status(thm)], ['1'])).
% 13.73/13.91  thf('77', plain,
% 13.73/13.91      (((r1_tarski @ (k1_tarski @ sk_B) @ k1_xboole_0) | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['75', '76'])).
% 13.73/13.91  thf('78', plain,
% 13.73/13.91      (![X10 : $i, X11 : $i]:
% 13.73/13.91         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 13.73/13.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.73/13.91  thf('79', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B))
% 13.73/13.91        | ((k3_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 13.73/13.91            = (k1_tarski @ sk_B)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['77', '78'])).
% 13.73/13.91  thf('80', plain,
% 13.73/13.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 13.73/13.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 13.73/13.91  thf('81', plain,
% 13.73/13.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 13.73/13.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 13.73/13.91  thf('82', plain,
% 13.73/13.91      (![X12 : $i]: ((k3_xboole_0 @ X12 @ k1_xboole_0) = (k1_xboole_0))),
% 13.73/13.91      inference('cnf', [status(esa)], [t2_boole])).
% 13.73/13.91  thf('83', plain,
% 13.73/13.91      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['81', '82'])).
% 13.73/13.91  thf('84', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B)) | ((k1_xboole_0) = (k1_tarski @ sk_B)))),
% 13.73/13.91      inference('demod', [status(thm)], ['79', '80', '83'])).
% 13.73/13.91  thf('85', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('86', plain,
% 13.73/13.91      (![X0 : $i]:
% 13.73/13.91         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 13.73/13.91          | ((sk_D_1) = (sk_B))
% 13.73/13.91          | ((X0) = (sk_B)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['84', '85'])).
% 13.73/13.91  thf('87', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['74', '86'])).
% 13.73/13.91  thf('88', plain, ((((sk_A) = (sk_B)) | ((sk_D_1) = (sk_B)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['87'])).
% 13.73/13.91  thf('89', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X33 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['66'])).
% 13.73/13.91  thf('90', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['48', '49'])).
% 13.73/13.91  thf('91', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i, X34 : $i]:
% 13.73/13.91         (((X34) = (X30))
% 13.73/13.91          | ((X34) = (X33))
% 13.73/13.91          | ~ (r2_hidden @ X34 @ (k2_tarski @ X33 @ X30)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['45'])).
% 13.73/13.91  thf('92', plain,
% 13.73/13.91      (![X0 : $i]:
% 13.73/13.91         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 13.73/13.91          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1))
% 13.73/13.91          | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91          | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91          | ((X0) = (sk_C))
% 13.73/13.91          | ((X0) = (sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['90', '91'])).
% 13.73/13.91  thf('93', plain,
% 13.73/13.91      ((((sk_A) = (sk_D_1))
% 13.73/13.91        | ((sk_A) = (sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['89', '92'])).
% 13.73/13.91  thf('94', plain, (((sk_A) != (sk_C))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('95', plain, (((sk_A) != (sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('96', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D_1)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['93', '94', '95'])).
% 13.73/13.91  thf('97', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X33 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['66'])).
% 13.73/13.91  thf('98', plain,
% 13.73/13.91      (((r2_hidden @ sk_A @ (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['96', '97'])).
% 13.73/13.91  thf('99', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('100', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((sk_A) = (sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['98', '99'])).
% 13.73/13.91  thf('101', plain, (((sk_A) != (sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('102', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 13.73/13.91  thf('103', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['51'])).
% 13.73/13.91  thf('104', plain,
% 13.73/13.91      (((r2_hidden @ sk_B @ (k1_tarski @ sk_C))
% 13.73/13.91        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['102', '103'])).
% 13.73/13.91  thf('105', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('106', plain,
% 13.73/13.91      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_B) = (sk_C)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['104', '105'])).
% 13.73/13.91  thf('107', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['51'])).
% 13.73/13.91  thf('108', plain, (((r2_hidden @ sk_B @ k1_xboole_0) | ((sk_B) = (sk_C)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['106', '107'])).
% 13.73/13.91  thf('109', plain,
% 13.73/13.91      (![X68 : $i, X70 : $i, X71 : $i]:
% 13.73/13.91         ((r1_tarski @ X70 @ (k2_tarski @ X68 @ X71))
% 13.73/13.91          | ((X70) != (k1_tarski @ X68)))),
% 13.73/13.91      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 13.73/13.91  thf('110', plain,
% 13.73/13.91      (![X68 : $i, X71 : $i]:
% 13.73/13.91         (r1_tarski @ (k1_tarski @ X68) @ (k2_tarski @ X68 @ X71))),
% 13.73/13.91      inference('simplify', [status(thm)], ['109'])).
% 13.73/13.91  thf('111', plain,
% 13.73/13.91      (![X0 : $i]:
% 13.73/13.91         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 13.73/13.91          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['5', '8'])).
% 13.73/13.91  thf('112', plain,
% 13.73/13.91      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('sup-', [status(thm)], ['110', '111'])).
% 13.73/13.91  thf('113', plain,
% 13.73/13.91      (![X68 : $i, X69 : $i, X70 : $i]:
% 13.73/13.91         (((X70) = (k2_tarski @ X68 @ X69))
% 13.73/13.91          | ((X70) = (k1_tarski @ X69))
% 13.73/13.91          | ((X70) = (k1_tarski @ X68))
% 13.73/13.91          | ((X70) = (k1_xboole_0))
% 13.73/13.91          | ~ (r1_tarski @ X70 @ (k2_tarski @ X68 @ X69)))),
% 13.73/13.91      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 13.73/13.91  thf('114', plain,
% 13.73/13.91      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k2_tarski @ sk_C @ sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['112', '113'])).
% 13.73/13.91  thf('115', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['51'])).
% 13.73/13.91  thf('116', plain,
% 13.73/13.91      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_A))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['114', '115'])).
% 13.73/13.91  thf('117', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('118', plain,
% 13.73/13.91      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1))
% 13.73/13.91        | ((sk_D_1) = (sk_A)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['116', '117'])).
% 13.73/13.91  thf('119', plain, (((sk_A) != (sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('120', plain,
% 13.73/13.91      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_D_1)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['118', '119'])).
% 13.73/13.91  thf('121', plain,
% 13.73/13.91      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 13.73/13.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 13.73/13.91  thf('122', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X30 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['51'])).
% 13.73/13.91  thf('123', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['121', '122'])).
% 13.73/13.91  thf('124', plain,
% 13.73/13.91      (((r2_hidden @ sk_D_1 @ (k1_tarski @ sk_A))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['120', '123'])).
% 13.73/13.91  thf('125', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('126', plain,
% 13.73/13.91      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C))
% 13.73/13.91        | ((sk_D_1) = (sk_A)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['124', '125'])).
% 13.73/13.91  thf('127', plain, (((sk_A) != (sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('128', plain,
% 13.73/13.91      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_tarski @ sk_C)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 13.73/13.91  thf('129', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 13.73/13.91      inference('sup+', [status(thm)], ['121', '122'])).
% 13.73/13.91  thf('130', plain,
% 13.73/13.91      (((r2_hidden @ sk_C @ (k1_tarski @ sk_A))
% 13.73/13.91        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['128', '129'])).
% 13.73/13.91  thf('131', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('132', plain,
% 13.73/13.91      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_C) = (sk_A)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['130', '131'])).
% 13.73/13.91  thf('133', plain, (((sk_A) != (sk_C))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('134', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['132', '133'])).
% 13.73/13.91  thf('135', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('136', plain,
% 13.73/13.91      (![X0 : $i]: (~ (r2_hidden @ X0 @ k1_xboole_0) | ((X0) = (sk_A)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['134', '135'])).
% 13.73/13.91  thf('137', plain, ((((sk_B) = (sk_C)) | ((sk_B) = (sk_A)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['108', '136'])).
% 13.73/13.91  thf('138', plain,
% 13.73/13.91      ((((sk_D_1) = (sk_C)) | ((sk_A) = (sk_B)) | ((sk_B) = (sk_A)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['88', '137'])).
% 13.73/13.91  thf('139', plain, ((((sk_A) = (sk_B)) | ((sk_D_1) = (sk_C)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['138'])).
% 13.73/13.91  thf('140', plain,
% 13.73/13.91      ((((sk_A) = (sk_D_1)) | ((sk_B) = (sk_C)) | ((sk_D_1) = (sk_C)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['47', '139'])).
% 13.73/13.91  thf('141', plain, (((sk_A) != (sk_D_1))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('142', plain, ((((sk_B) = (sk_C)) | ((sk_D_1) = (sk_C)))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['140', '141'])).
% 13.73/13.91  thf('143', plain, ((((sk_B) = (sk_C)) | ((sk_B) = (sk_D_1)))),
% 13.73/13.91      inference('sup-', [status(thm)], ['44', '46'])).
% 13.73/13.91  thf('144', plain, ((((sk_D_1) != (sk_C)) | ((sk_B) = (sk_C)))),
% 13.73/13.91      inference('eq_fact', [status(thm)], ['143'])).
% 13.73/13.91  thf('145', plain, (((sk_B) = (sk_C))),
% 13.73/13.91      inference('clc', [status(thm)], ['142', '144'])).
% 13.73/13.91  thf('146', plain,
% 13.73/13.91      ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_C @ sk_D_1))),
% 13.73/13.91      inference('demod', [status(thm)], ['0', '145'])).
% 13.73/13.91  thf('147', plain, ((((sk_A) = (sk_B)) | ((sk_D_1) = (sk_C)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['138'])).
% 13.73/13.91  thf('148', plain, (((sk_B) = (sk_C))),
% 13.73/13.91      inference('clc', [status(thm)], ['142', '144'])).
% 13.73/13.91  thf('149', plain, ((((sk_A) = (sk_C)) | ((sk_D_1) = (sk_C)))),
% 13.73/13.91      inference('sup+', [status(thm)], ['147', '148'])).
% 13.73/13.91  thf('150', plain, (((sk_A) != (sk_C))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('151', plain, (((sk_D_1) = (sk_C))),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['149', '150'])).
% 13.73/13.91  thf('152', plain,
% 13.73/13.91      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 13.73/13.91      inference('cnf', [status(esa)], [t69_enumset1])).
% 13.73/13.91  thf('153', plain,
% 13.73/13.91      ((r1_tarski @ (k2_tarski @ sk_A @ sk_C) @ (k1_tarski @ sk_C))),
% 13.73/13.91      inference('demod', [status(thm)], ['146', '151', '152'])).
% 13.73/13.91  thf('154', plain,
% 13.73/13.91      (![X10 : $i, X11 : $i]:
% 13.73/13.91         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 13.73/13.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.73/13.91  thf('155', plain,
% 13.73/13.91      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k1_tarski @ sk_C))
% 13.73/13.91         = (k2_tarski @ sk_A @ sk_C))),
% 13.73/13.91      inference('sup-', [status(thm)], ['153', '154'])).
% 13.73/13.91  thf('156', plain,
% 13.73/13.91      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 13.73/13.91      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 13.73/13.91  thf('157', plain,
% 13.73/13.91      (![X68 : $i, X71 : $i]:
% 13.73/13.91         (r1_tarski @ (k1_tarski @ X71) @ (k2_tarski @ X68 @ X71))),
% 13.73/13.91      inference('simplify', [status(thm)], ['1'])).
% 13.73/13.91  thf('158', plain,
% 13.73/13.91      (![X10 : $i, X11 : $i]:
% 13.73/13.91         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 13.73/13.91      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.73/13.91  thf('159', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 13.73/13.91           = (k1_tarski @ X0))),
% 13.73/13.91      inference('sup-', [status(thm)], ['157', '158'])).
% 13.73/13.91  thf('160', plain, (((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_C))),
% 13.73/13.91      inference('demod', [status(thm)], ['155', '156', '159'])).
% 13.73/13.91  thf('161', plain,
% 13.73/13.91      (![X30 : $i, X33 : $i]: (r2_hidden @ X33 @ (k2_tarski @ X33 @ X30))),
% 13.73/13.91      inference('simplify', [status(thm)], ['66'])).
% 13.73/13.91  thf('162', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C))),
% 13.73/13.91      inference('sup+', [status(thm)], ['160', '161'])).
% 13.73/13.91  thf('163', plain,
% 13.73/13.91      (![X0 : $i, X1 : $i]:
% 13.73/13.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 13.73/13.91      inference('simplify', [status(thm)], ['62'])).
% 13.73/13.91  thf('164', plain, (((sk_A) = (sk_C))),
% 13.73/13.91      inference('sup-', [status(thm)], ['162', '163'])).
% 13.73/13.91  thf('165', plain, (((sk_A) != (sk_C))),
% 13.73/13.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.73/13.91  thf('166', plain, ($false),
% 13.73/13.91      inference('simplify_reflect-', [status(thm)], ['164', '165'])).
% 13.73/13.91  
% 13.73/13.91  % SZS output end Refutation
% 13.73/13.91  
% 13.73/13.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
