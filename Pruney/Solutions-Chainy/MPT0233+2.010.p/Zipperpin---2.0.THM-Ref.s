%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QUFTZyLnhH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:38 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 121 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  710 ( 879 expanded)
%              Number of equality atoms :   76 (  96 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( X26 = X27 )
      | ( X26 = X28 )
      | ( X26 = X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X69 ) @ ( k2_tarski @ X69 @ X70 ) )
      = ( k1_tarski @ X69 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k3_xboole_0 @ X17 @ X18 )
        = X17 )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( r1_xboole_0 @ X22 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X5 @ X8 ) )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','33'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('38',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D ) )
    = ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('40',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('41',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( k2_enumset1 @ X37 @ X38 @ X39 @ X40 )
      = ( k2_xboole_0 @ ( k2_tarski @ X37 @ X38 ) @ ( k2_tarski @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('43',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X44 @ X44 @ X45 @ X46 )
      = ( k1_enumset1 @ X44 @ X45 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('44',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k2_tarski @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['39','42','43'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D ) )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k1_enumset1 @ X42 @ X42 @ X43 )
      = ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('49',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ X34 )
      | ~ ( zip_tseitin_0 @ X35 @ X31 @ X32 @ X33 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X31 @ X32 @ X33 )
      | ~ ( r2_hidden @ X35 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_C_1 )
      | ( X0 = sk_C_1 )
      | ( X0 = sk_D )
      | ( zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A )
      | ( X0 = sk_D )
      | ( X0 = sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('59',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QUFTZyLnhH
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:04 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.83  % Solved by: fo/fo7.sh
% 0.61/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.83  % done 1028 iterations in 0.370s
% 0.61/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.83  % SZS output start Refutation
% 0.61/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.61/0.83  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.61/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.61/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.61/0.83  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.61/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.83  thf(d1_enumset1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.61/0.83       ( ![E:$i]:
% 0.61/0.83         ( ( r2_hidden @ E @ D ) <=>
% 0.61/0.83           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_0, axiom,
% 0.61/0.83    (![E:$i,C:$i,B:$i,A:$i]:
% 0.61/0.83     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.61/0.83       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.61/0.83  thf('0', plain,
% 0.61/0.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.61/0.83         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 0.61/0.83          | ((X26) = (X27))
% 0.61/0.83          | ((X26) = (X28))
% 0.61/0.83          | ((X26) = (X29)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf(t19_zfmisc_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.61/0.83       ( k1_tarski @ A ) ))).
% 0.61/0.83  thf('1', plain,
% 0.61/0.83      (![X69 : $i, X70 : $i]:
% 0.61/0.83         ((k3_xboole_0 @ (k1_tarski @ X69) @ (k2_tarski @ X69 @ X70))
% 0.61/0.83           = (k1_tarski @ X69))),
% 0.61/0.83      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.61/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.61/0.83  thf('2', plain,
% 0.61/0.83      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.61/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.83  thf(t17_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.61/0.83  thf('3', plain,
% 0.61/0.83      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.61/0.83      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.61/0.83  thf('4', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.61/0.83      inference('sup+', [status(thm)], ['2', '3'])).
% 0.61/0.83  thf(t28_zfmisc_1, conjecture,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.61/0.83          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.61/0.83  thf(zf_stmt_1, negated_conjecture,
% 0.61/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.61/0.83             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.61/0.83    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.61/0.83  thf('5', plain,
% 0.61/0.83      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.83  thf(t28_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.61/0.83  thf('6', plain,
% 0.61/0.83      (![X17 : $i, X18 : $i]:
% 0.61/0.83         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.61/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.83  thf('7', plain,
% 0.61/0.83      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.61/0.83         (k2_tarski @ sk_C_1 @ sk_D)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.61/0.83  thf('8', plain,
% 0.61/0.83      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.61/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.61/0.83  thf(t18_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.61/0.83  thf('9', plain,
% 0.61/0.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.61/0.83         ((r1_tarski @ X14 @ X15)
% 0.61/0.83          | ~ (r1_tarski @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.61/0.83  thf('10', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.83         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['8', '9'])).
% 0.61/0.83  thf('11', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.61/0.83          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['7', '10'])).
% 0.61/0.83  thf('12', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (r1_tarski @ (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B_1)) @ 
% 0.61/0.83          (k2_tarski @ sk_C_1 @ sk_D))),
% 0.61/0.83      inference('sup-', [status(thm)], ['4', '11'])).
% 0.61/0.83  thf('13', plain,
% 0.61/0.83      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))),
% 0.61/0.83      inference('sup+', [status(thm)], ['1', '12'])).
% 0.61/0.83  thf('14', plain,
% 0.61/0.83      (![X17 : $i, X18 : $i]:
% 0.61/0.83         (((k3_xboole_0 @ X17 @ X18) = (X17)) | ~ (r1_tarski @ X17 @ X18))),
% 0.61/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.61/0.83  thf('15', plain,
% 0.61/0.83      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.61/0.83         = (k1_tarski @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.61/0.83  thf(t100_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.61/0.83  thf('16', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X10 @ X11)
% 0.61/0.83           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.83  thf('17', plain,
% 0.61/0.83      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.61/0.83         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['15', '16'])).
% 0.61/0.83  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.61/0.83  thf('18', plain, (![X22 : $i]: (r1_xboole_0 @ X22 @ k1_xboole_0)),
% 0.61/0.83      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.61/0.83  thf(t7_xboole_0, axiom,
% 0.61/0.83    (![A:$i]:
% 0.61/0.83     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.61/0.83          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.61/0.83  thf('19', plain,
% 0.61/0.83      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.61/0.83      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.61/0.83  thf(t4_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.61/0.83            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.61/0.83  thf('20', plain,
% 0.61/0.83      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X7 @ (k3_xboole_0 @ X5 @ X8))
% 0.61/0.83          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.61/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.61/0.83  thf('21', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]:
% 0.61/0.83         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.61/0.83  thf('22', plain,
% 0.61/0.83      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['18', '21'])).
% 0.61/0.83  thf('23', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X10 @ X11)
% 0.61/0.83           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.83  thf('24', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['22', '23'])).
% 0.61/0.83  thf(t5_boole, axiom,
% 0.61/0.83    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.61/0.83  thf('25', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.61/0.83      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.83  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.61/0.83      inference('demod', [status(thm)], ['24', '25'])).
% 0.61/0.83  thf(t48_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.83  thf('27', plain,
% 0.61/0.83      (![X19 : $i, X20 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.61/0.83           = (k3_xboole_0 @ X19 @ X20))),
% 0.61/0.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.61/0.83  thf('28', plain,
% 0.61/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['26', '27'])).
% 0.61/0.83  thf(idempotence_k3_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.61/0.83  thf('29', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.61/0.83      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.61/0.83  thf('30', plain,
% 0.61/0.83      (![X10 : $i, X11 : $i]:
% 0.61/0.83         ((k4_xboole_0 @ X10 @ X11)
% 0.61/0.83           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.61/0.83  thf('31', plain,
% 0.61/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['29', '30'])).
% 0.61/0.83  thf('32', plain,
% 0.61/0.83      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.61/0.83      inference('sup-', [status(thm)], ['18', '21'])).
% 0.61/0.83  thf('33', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.61/0.83  thf('34', plain,
% 0.61/0.83      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.61/0.83         = (k1_xboole_0))),
% 0.61/0.83      inference('demod', [status(thm)], ['17', '33'])).
% 0.61/0.83  thf(t98_xboole_1, axiom,
% 0.61/0.83    (![A:$i,B:$i]:
% 0.61/0.83     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.61/0.83  thf('35', plain,
% 0.61/0.83      (![X23 : $i, X24 : $i]:
% 0.61/0.83         ((k2_xboole_0 @ X23 @ X24)
% 0.61/0.83           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.61/0.83      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.61/0.83  thf('36', plain,
% 0.61/0.83      (((k2_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D) @ (k1_tarski @ sk_A))
% 0.61/0.83         = (k5_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D) @ k1_xboole_0))),
% 0.61/0.83      inference('sup+', [status(thm)], ['34', '35'])).
% 0.61/0.83  thf(commutativity_k2_xboole_0, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.61/0.83  thf('37', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.61/0.83      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.61/0.83  thf('38', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 0.61/0.83      inference('cnf', [status(esa)], [t5_boole])).
% 0.61/0.83  thf('39', plain,
% 0.61/0.83      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.61/0.83         = (k2_tarski @ sk_C_1 @ sk_D))),
% 0.61/0.83      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.61/0.83  thf(t69_enumset1, axiom,
% 0.61/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.83  thf('40', plain,
% 0.61/0.83      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.61/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.83  thf(l53_enumset1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.61/0.83       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.61/0.83  thf('41', plain,
% 0.61/0.83      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.61/0.83         ((k2_enumset1 @ X37 @ X38 @ X39 @ X40)
% 0.61/0.83           = (k2_xboole_0 @ (k2_tarski @ X37 @ X38) @ (k2_tarski @ X39 @ X40)))),
% 0.61/0.83      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.61/0.83  thf('42', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.83         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.61/0.83           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.61/0.83      inference('sup+', [status(thm)], ['40', '41'])).
% 0.61/0.83  thf(t71_enumset1, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i]:
% 0.61/0.83     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.61/0.83  thf('43', plain,
% 0.61/0.83      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.61/0.83         ((k2_enumset1 @ X44 @ X44 @ X45 @ X46)
% 0.61/0.83           = (k1_enumset1 @ X44 @ X45 @ X46))),
% 0.61/0.83      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.61/0.83  thf('44', plain,
% 0.61/0.83      (((k1_enumset1 @ sk_A @ sk_C_1 @ sk_D) = (k2_tarski @ sk_C_1 @ sk_D))),
% 0.61/0.83      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.61/0.83  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.61/0.83  thf(zf_stmt_3, axiom,
% 0.61/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.83     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.61/0.83       ( ![E:$i]:
% 0.61/0.83         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.61/0.83  thf('45', plain,
% 0.61/0.83      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.61/0.83         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.61/0.83          | (r2_hidden @ X30 @ X34)
% 0.61/0.83          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.83  thf('46', plain,
% 0.61/0.83      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.61/0.83         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.61/0.83          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.61/0.83      inference('simplify', [status(thm)], ['45'])).
% 0.61/0.83  thf('47', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((r2_hidden @ X0 @ (k2_tarski @ sk_C_1 @ sk_D))
% 0.61/0.83          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A))),
% 0.61/0.83      inference('sup+', [status(thm)], ['44', '46'])).
% 0.61/0.83  thf(t70_enumset1, axiom,
% 0.61/0.83    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.61/0.83  thf('48', plain,
% 0.61/0.83      (![X42 : $i, X43 : $i]:
% 0.61/0.83         ((k1_enumset1 @ X42 @ X42 @ X43) = (k2_tarski @ X42 @ X43))),
% 0.61/0.83      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.83  thf('49', plain,
% 0.61/0.83      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X35 @ X34)
% 0.61/0.83          | ~ (zip_tseitin_0 @ X35 @ X31 @ X32 @ X33)
% 0.61/0.83          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.83  thf('50', plain,
% 0.61/0.83      (![X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.61/0.83         (~ (zip_tseitin_0 @ X35 @ X31 @ X32 @ X33)
% 0.61/0.83          | ~ (r2_hidden @ X35 @ (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['49'])).
% 0.61/0.83  thf('51', plain,
% 0.61/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.83         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.61/0.83          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['48', '50'])).
% 0.61/0.83  thf('52', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A)
% 0.61/0.83          | ~ (zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_C_1))),
% 0.61/0.83      inference('sup-', [status(thm)], ['47', '51'])).
% 0.61/0.83  thf('53', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         (((X0) = (sk_C_1))
% 0.61/0.83          | ((X0) = (sk_C_1))
% 0.61/0.83          | ((X0) = (sk_D))
% 0.61/0.83          | (zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A))),
% 0.61/0.83      inference('sup-', [status(thm)], ['0', '52'])).
% 0.61/0.83  thf('54', plain,
% 0.61/0.83      (![X0 : $i]:
% 0.61/0.83         ((zip_tseitin_0 @ X0 @ sk_D @ sk_C_1 @ sk_A)
% 0.61/0.83          | ((X0) = (sk_D))
% 0.61/0.83          | ((X0) = (sk_C_1)))),
% 0.61/0.83      inference('simplify', [status(thm)], ['53'])).
% 0.61/0.83  thf('55', plain,
% 0.61/0.83      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.61/0.83         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.83  thf('56', plain,
% 0.61/0.83      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.61/0.83         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 0.61/0.83      inference('simplify', [status(thm)], ['55'])).
% 0.61/0.83  thf('57', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_D)))),
% 0.61/0.83      inference('sup-', [status(thm)], ['54', '56'])).
% 0.61/0.83  thf('58', plain, (((sk_A) != (sk_D))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.83  thf('59', plain, (((sk_A) != (sk_C_1))),
% 0.61/0.83      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.61/0.83  thf('60', plain, ($false),
% 0.61/0.83      inference('simplify_reflect-', [status(thm)], ['57', '58', '59'])).
% 0.61/0.83  
% 0.61/0.83  % SZS output end Refutation
% 0.61/0.83  
% 0.61/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
