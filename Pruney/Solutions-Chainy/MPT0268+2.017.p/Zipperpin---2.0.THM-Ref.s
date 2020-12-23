%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rVRDHowzE6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:54 EST 2020

% Result     : Theorem 0.80s
% Output     : Refutation 0.80s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 126 expanded)
%              Number of leaves         :   28 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  708 ( 997 expanded)
%              Number of equality atoms :   65 (  88 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X58 ) @ X59 )
      | ( r2_hidden @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('8',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('10',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B_1 @ X0 )
        | ( r2_hidden @ sk_B_1 @ ( k3_xboole_0 @ X0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_B_1 @ ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('24',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
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

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B_1 @ k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
        = sk_A )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','34'])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('37',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('38',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('44',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('48',plain,(
    ! [X2: $i] :
      ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('51',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X58 ) @ X59 )
      | ( r2_hidden @ X58 @ X59 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('58',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('64',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','49','50','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rVRDHowzE6
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.80/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.80/1.03  % Solved by: fo/fo7.sh
% 0.80/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.80/1.03  % done 1236 iterations in 0.569s
% 0.80/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.80/1.03  % SZS output start Refutation
% 0.80/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.80/1.03  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.80/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.80/1.03  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.80/1.03  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.80/1.03  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.80/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.80/1.03  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.80/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.80/1.03  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.80/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.80/1.03  thf(t65_zfmisc_1, conjecture,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.80/1.03       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.80/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.80/1.03    (~( ![A:$i,B:$i]:
% 0.80/1.03        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.80/1.03          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.80/1.03    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.80/1.03  thf('0', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)
% 0.80/1.03        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('1', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['0'])).
% 0.80/1.03  thf('2', plain,
% 0.80/1.03      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 0.80/1.03        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.80/1.03  thf('3', plain,
% 0.80/1.03      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('split', [status(esa)], ['2'])).
% 0.80/1.03  thf(t79_xboole_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.80/1.03  thf('4', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.80/1.03      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.80/1.03  thf('5', plain,
% 0.80/1.03      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('sup+', [status(thm)], ['3', '4'])).
% 0.80/1.03  thf(l27_zfmisc_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.80/1.03  thf('6', plain,
% 0.80/1.03      (![X58 : $i, X59 : $i]:
% 0.80/1.03         ((r1_xboole_0 @ (k1_tarski @ X58) @ X59) | (r2_hidden @ X58 @ X59))),
% 0.80/1.03      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.80/1.03  thf(t7_xboole_0, axiom,
% 0.80/1.03    (![A:$i]:
% 0.80/1.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.80/1.03          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.80/1.03  thf('7', plain,
% 0.80/1.03      (![X12 : $i]:
% 0.80/1.03         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/1.03  thf('8', plain,
% 0.80/1.03      (![X12 : $i]:
% 0.80/1.03         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/1.03  thf(d4_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i]:
% 0.80/1.03     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.80/1.03       ( ![D:$i]:
% 0.80/1.03         ( ( r2_hidden @ D @ C ) <=>
% 0.80/1.03           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.80/1.03  thf('9', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ X3)
% 0.80/1.03          | ~ (r2_hidden @ X2 @ X4)
% 0.80/1.03          | (r2_hidden @ X2 @ X5)
% 0.80/1.03          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.80/1.03      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.80/1.03  thf('10', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.80/1.03         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.80/1.03          | ~ (r2_hidden @ X2 @ X4)
% 0.80/1.03          | ~ (r2_hidden @ X2 @ X3))),
% 0.80/1.03      inference('simplify', [status(thm)], ['9'])).
% 0.80/1.03  thf('11', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((X0) = (k1_xboole_0))
% 0.80/1.03          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.80/1.03          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['8', '10'])).
% 0.80/1.03  thf('12', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         (((X0) = (k1_xboole_0))
% 0.80/1.03          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.80/1.03          | ((X0) = (k1_xboole_0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['7', '11'])).
% 0.80/1.03  thf('13', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.80/1.03          | ((X0) = (k1_xboole_0)))),
% 0.80/1.03      inference('simplify', [status(thm)], ['12'])).
% 0.80/1.03  thf(t4_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.03            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.80/1.03       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.80/1.03            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.80/1.03  thf('14', plain,
% 0.80/1.03      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.80/1.03          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('15', plain,
% 0.80/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['13', '14'])).
% 0.80/1.03  thf('16', plain,
% 0.80/1.03      (![X0 : $i]:
% 0.80/1.03         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.80/1.03          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['6', '15'])).
% 0.80/1.03  thf('17', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['0'])).
% 0.80/1.03  thf('18', plain,
% 0.80/1.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.80/1.03         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.80/1.03          | ~ (r2_hidden @ X2 @ X4)
% 0.80/1.03          | ~ (r2_hidden @ X2 @ X3))),
% 0.80/1.03      inference('simplify', [status(thm)], ['9'])).
% 0.80/1.03  thf('19', plain,
% 0.80/1.03      ((![X0 : $i]:
% 0.80/1.03          (~ (r2_hidden @ sk_B_1 @ X0)
% 0.80/1.03           | (r2_hidden @ sk_B_1 @ (k3_xboole_0 @ X0 @ sk_A))))
% 0.80/1.03         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['17', '18'])).
% 0.80/1.03  thf('20', plain,
% 0.80/1.03      (((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.80/1.03         | (r2_hidden @ sk_B_1 @ (k3_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))))
% 0.80/1.03         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['16', '19'])).
% 0.80/1.03  thf(commutativity_k3_xboole_0, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.80/1.03  thf('21', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.03  thf('22', plain,
% 0.80/1.03      (((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.80/1.03         | (r2_hidden @ sk_B_1 @ (k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))))
% 0.80/1.03         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('demod', [status(thm)], ['20', '21'])).
% 0.80/1.03  thf('23', plain,
% 0.80/1.03      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.80/1.03          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('24', plain,
% 0.80/1.03      (((((k1_tarski @ sk_B_1) = (k1_xboole_0))
% 0.80/1.03         | ~ (r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1))))
% 0.80/1.03         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['22', '23'])).
% 0.80/1.03  thf('25', plain,
% 0.80/1.03      ((((k1_tarski @ sk_B_1) = (k1_xboole_0)))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 0.80/1.03             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['5', '24'])).
% 0.80/1.03  thf(t69_enumset1, axiom,
% 0.80/1.03    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.80/1.03  thf('26', plain,
% 0.80/1.03      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.80/1.03      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.80/1.03  thf(t70_enumset1, axiom,
% 0.80/1.03    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.80/1.03  thf('27', plain,
% 0.80/1.03      (![X31 : $i, X32 : $i]:
% 0.80/1.03         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.80/1.03      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.80/1.03  thf(d1_enumset1, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.80/1.03       ( ![E:$i]:
% 0.80/1.03         ( ( r2_hidden @ E @ D ) <=>
% 0.80/1.03           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.80/1.03  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.80/1.03  thf(zf_stmt_2, axiom,
% 0.80/1.03    (![E:$i,C:$i,B:$i,A:$i]:
% 0.80/1.03     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.80/1.03       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.80/1.03  thf(zf_stmt_3, axiom,
% 0.80/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.80/1.03     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.80/1.03       ( ![E:$i]:
% 0.80/1.03         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.80/1.03  thf('28', plain,
% 0.80/1.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.80/1.03         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.80/1.03          | (r2_hidden @ X23 @ X27)
% 0.80/1.03          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.80/1.03  thf('29', plain,
% 0.80/1.03      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.80/1.03         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 0.80/1.03          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 0.80/1.03      inference('simplify', [status(thm)], ['28'])).
% 0.80/1.03  thf('30', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.80/1.03          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.80/1.03      inference('sup+', [status(thm)], ['27', '29'])).
% 0.80/1.03  thf('31', plain,
% 0.80/1.03      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.80/1.03         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 0.80/1.03      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.80/1.03  thf('32', plain,
% 0.80/1.03      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.80/1.03         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 0.80/1.03      inference('simplify', [status(thm)], ['31'])).
% 0.80/1.03  thf('33', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['30', '32'])).
% 0.80/1.03  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['26', '33'])).
% 0.80/1.03  thf('35', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ k1_xboole_0))
% 0.80/1.03         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))) & 
% 0.80/1.03             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['25', '34'])).
% 0.80/1.03  thf('36', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.80/1.03      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.80/1.03  thf('37', plain,
% 0.80/1.03      (![X12 : $i]:
% 0.80/1.03         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.80/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.80/1.03  thf('38', plain,
% 0.80/1.03      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.80/1.03          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('39', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.80/1.03  thf('40', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['36', '39'])).
% 0.80/1.03  thf('41', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.03  thf('42', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.80/1.03      inference('demod', [status(thm)], ['40', '41'])).
% 0.80/1.03  thf('43', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.03  thf('44', plain,
% 0.80/1.03      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.80/1.03          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.80/1.03      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.80/1.03  thf('45', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.80/1.03          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('sup-', [status(thm)], ['43', '44'])).
% 0.80/1.03  thf('46', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.80/1.03         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.80/1.03          | ~ (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['42', '45'])).
% 0.80/1.03  thf('47', plain,
% 0.80/1.03      (![X16 : $i, X17 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X17)),
% 0.80/1.03      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.80/1.03  thf('48', plain, (![X2 : $i]: ~ (r2_hidden @ X2 @ k1_xboole_0)),
% 0.80/1.03      inference('demod', [status(thm)], ['46', '47'])).
% 0.80/1.03  thf('49', plain,
% 0.80/1.03      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['35', '48'])).
% 0.80/1.03  thf('50', plain,
% 0.80/1.03      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['2'])).
% 0.80/1.03  thf('51', plain,
% 0.80/1.03      (![X58 : $i, X59 : $i]:
% 0.80/1.03         ((r1_xboole_0 @ (k1_tarski @ X58) @ X59) | (r2_hidden @ X58 @ X59))),
% 0.80/1.03      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.80/1.03  thf('52', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.80/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.80/1.03  thf('53', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((r2_hidden @ X1 @ X0)
% 0.80/1.03          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['51', '52'])).
% 0.80/1.03  thf('54', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.80/1.03      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.80/1.03  thf(t100_xboole_1, axiom,
% 0.80/1.03    (![A:$i,B:$i]:
% 0.80/1.03     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.80/1.03  thf('55', plain,
% 0.80/1.03      (![X13 : $i, X14 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X13 @ X14)
% 0.80/1.03           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.80/1.03      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.80/1.03  thf('56', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         ((k4_xboole_0 @ X0 @ X1)
% 0.80/1.03           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.80/1.03      inference('sup+', [status(thm)], ['54', '55'])).
% 0.80/1.03  thf('57', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 0.80/1.03            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.80/1.03          | (r2_hidden @ X1 @ X0))),
% 0.80/1.03      inference('sup+', [status(thm)], ['53', '56'])).
% 0.80/1.03  thf(t5_boole, axiom,
% 0.80/1.03    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.80/1.03  thf('58', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.80/1.03      inference('cnf', [status(esa)], [t5_boole])).
% 0.80/1.03  thf('59', plain,
% 0.80/1.03      (![X0 : $i, X1 : $i]:
% 0.80/1.03         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 0.80/1.03          | (r2_hidden @ X1 @ X0))),
% 0.80/1.03      inference('demod', [status(thm)], ['57', '58'])).
% 0.80/1.03  thf('60', plain,
% 0.80/1.03      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 0.80/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('split', [status(esa)], ['0'])).
% 0.80/1.03  thf('61', plain,
% 0.80/1.03      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 0.80/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('sup-', [status(thm)], ['59', '60'])).
% 0.80/1.03  thf('62', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A))
% 0.80/1.03         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 0.80/1.03      inference('simplify', [status(thm)], ['61'])).
% 0.80/1.03  thf('63', plain,
% 0.80/1.03      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.80/1.03      inference('split', [status(esa)], ['2'])).
% 0.80/1.03  thf('64', plain,
% 0.80/1.03      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.80/1.03       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 0.80/1.03      inference('sup-', [status(thm)], ['62', '63'])).
% 0.80/1.03  thf('65', plain, ($false),
% 0.80/1.03      inference('sat_resolution*', [status(thm)], ['1', '49', '50', '64'])).
% 0.80/1.03  
% 0.80/1.03  % SZS output end Refutation
% 0.80/1.03  
% 0.80/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
