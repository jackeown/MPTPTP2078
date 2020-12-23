%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AOWBO74dsg

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:59 EST 2020

% Result     : Theorem 1.22s
% Output     : Refutation 1.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 184 expanded)
%              Number of leaves         :   28 (  64 expanded)
%              Depth                    :   14
%              Number of atoms          :  769 (1552 expanded)
%              Number of equality atoms :   69 ( 125 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
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

thf('16',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('33',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','42'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('46',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('50',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('51',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','54'])).

thf('56',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','59'])).

thf('61',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','67'])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('70',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('73',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AOWBO74dsg
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.22/1.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.22/1.50  % Solved by: fo/fo7.sh
% 1.22/1.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.22/1.50  % done 1673 iterations in 1.043s
% 1.22/1.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.22/1.50  % SZS output start Refutation
% 1.22/1.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.22/1.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.22/1.50  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.22/1.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.22/1.50  thf(sk_A_type, type, sk_A: $i).
% 1.22/1.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.22/1.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.22/1.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.22/1.50  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.22/1.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.22/1.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.22/1.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.22/1.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.22/1.50  thf(sk_B_type, type, sk_B: $i > $i).
% 1.22/1.50  thf(t65_zfmisc_1, conjecture,
% 1.22/1.50    (![A:$i,B:$i]:
% 1.22/1.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.22/1.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.22/1.50  thf(zf_stmt_0, negated_conjecture,
% 1.22/1.50    (~( ![A:$i,B:$i]:
% 1.22/1.50        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.22/1.50          ( ~( r2_hidden @ B @ A ) ) ) )),
% 1.22/1.50    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 1.22/1.50  thf('0', plain,
% 1.22/1.50      (((r2_hidden @ sk_B_1 @ sk_A)
% 1.22/1.50        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 1.22/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.50  thf('1', plain,
% 1.22/1.50      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.22/1.50       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.22/1.50      inference('split', [status(esa)], ['0'])).
% 1.22/1.50  thf('2', plain,
% 1.22/1.50      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.22/1.50      inference('split', [status(esa)], ['0'])).
% 1.22/1.50  thf('3', plain,
% 1.22/1.50      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 1.22/1.50        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.22/1.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.22/1.50  thf('4', plain,
% 1.22/1.50      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 1.22/1.50         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('split', [status(esa)], ['3'])).
% 1.22/1.50  thf(t79_xboole_1, axiom,
% 1.22/1.50    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.22/1.50  thf('5', plain,
% 1.22/1.50      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 1.22/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.22/1.50  thf('6', plain,
% 1.22/1.50      (((r1_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)))
% 1.22/1.50         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('sup+', [status(thm)], ['4', '5'])).
% 1.22/1.50  thf(t3_xboole_0, axiom,
% 1.22/1.50    (![A:$i,B:$i]:
% 1.22/1.50     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.22/1.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.22/1.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.22/1.50            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.22/1.50  thf('7', plain,
% 1.22/1.50      (![X6 : $i, X7 : $i]:
% 1.22/1.50         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.22/1.50  thf('8', plain,
% 1.22/1.50      (![X6 : $i, X7 : $i]:
% 1.22/1.50         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.22/1.50  thf('9', plain,
% 1.22/1.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.22/1.50         (~ (r2_hidden @ X8 @ X6)
% 1.22/1.50          | ~ (r2_hidden @ X8 @ X9)
% 1.22/1.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.22/1.50  thf('10', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.50         ((r1_xboole_0 @ X1 @ X0)
% 1.22/1.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.22/1.50          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 1.22/1.50      inference('sup-', [status(thm)], ['8', '9'])).
% 1.22/1.50  thf('11', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         ((r1_xboole_0 @ X0 @ X1)
% 1.22/1.50          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.22/1.50          | (r1_xboole_0 @ X0 @ X1))),
% 1.22/1.50      inference('sup-', [status(thm)], ['7', '10'])).
% 1.22/1.50  thf('12', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.22/1.50      inference('simplify', [status(thm)], ['11'])).
% 1.22/1.50  thf('13', plain,
% 1.22/1.50      (((r1_xboole_0 @ (k1_tarski @ sk_B_1) @ sk_A))
% 1.22/1.50         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('sup-', [status(thm)], ['6', '12'])).
% 1.22/1.50  thf(t69_enumset1, axiom,
% 1.22/1.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.22/1.50  thf('14', plain,
% 1.22/1.50      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 1.22/1.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.22/1.50  thf(t70_enumset1, axiom,
% 1.22/1.50    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.22/1.50  thf('15', plain,
% 1.22/1.50      (![X29 : $i, X30 : $i]:
% 1.22/1.50         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 1.22/1.50      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.22/1.50  thf(d1_enumset1, axiom,
% 1.22/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.22/1.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.22/1.50       ( ![E:$i]:
% 1.22/1.50         ( ( r2_hidden @ E @ D ) <=>
% 1.22/1.50           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.22/1.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.22/1.50  thf(zf_stmt_2, axiom,
% 1.22/1.50    (![E:$i,C:$i,B:$i,A:$i]:
% 1.22/1.50     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.22/1.50       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.22/1.50  thf(zf_stmt_3, axiom,
% 1.22/1.50    (![A:$i,B:$i,C:$i,D:$i]:
% 1.22/1.50     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.22/1.50       ( ![E:$i]:
% 1.22/1.50         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.22/1.50  thf('16', plain,
% 1.22/1.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.22/1.50         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 1.22/1.50          | (r2_hidden @ X21 @ X25)
% 1.22/1.50          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 1.22/1.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.22/1.50  thf('17', plain,
% 1.22/1.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.22/1.50         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 1.22/1.50          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 1.22/1.50      inference('simplify', [status(thm)], ['16'])).
% 1.22/1.50  thf('18', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.50         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.22/1.50          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.22/1.50      inference('sup+', [status(thm)], ['15', '17'])).
% 1.22/1.50  thf('19', plain,
% 1.22/1.50      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.22/1.50         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 1.22/1.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.22/1.50  thf('20', plain,
% 1.22/1.50      (![X16 : $i, X18 : $i, X19 : $i]:
% 1.22/1.50         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 1.22/1.50      inference('simplify', [status(thm)], ['19'])).
% 1.22/1.50  thf('21', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.22/1.50      inference('sup-', [status(thm)], ['18', '20'])).
% 1.22/1.50  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.22/1.50      inference('sup+', [status(thm)], ['14', '21'])).
% 1.22/1.50  thf('23', plain,
% 1.22/1.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.22/1.50         (~ (r2_hidden @ X8 @ X6)
% 1.22/1.50          | ~ (r2_hidden @ X8 @ X9)
% 1.22/1.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.22/1.50  thf('24', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 1.22/1.50      inference('sup-', [status(thm)], ['22', '23'])).
% 1.22/1.50  thf('25', plain,
% 1.22/1.50      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 1.22/1.50         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('sup-', [status(thm)], ['13', '24'])).
% 1.22/1.50  thf('26', plain,
% 1.22/1.50      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.22/1.50       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.22/1.50      inference('sup-', [status(thm)], ['2', '25'])).
% 1.22/1.50  thf('27', plain,
% 1.22/1.50      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.22/1.50       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.22/1.50      inference('split', [status(esa)], ['3'])).
% 1.22/1.50  thf(l27_zfmisc_1, axiom,
% 1.22/1.50    (![A:$i,B:$i]:
% 1.22/1.50     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.22/1.50  thf('28', plain,
% 1.22/1.50      (![X38 : $i, X39 : $i]:
% 1.22/1.50         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 1.22/1.50      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.22/1.50  thf('29', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 1.22/1.50      inference('simplify', [status(thm)], ['11'])).
% 1.22/1.50  thf('30', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 1.22/1.50      inference('sup-', [status(thm)], ['28', '29'])).
% 1.22/1.50  thf(t7_xboole_0, axiom,
% 1.22/1.50    (![A:$i]:
% 1.22/1.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.22/1.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.22/1.50  thf('31', plain,
% 1.22/1.50      (![X10 : $i]:
% 1.22/1.50         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.22/1.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.22/1.50  thf(d4_xboole_0, axiom,
% 1.22/1.50    (![A:$i,B:$i,C:$i]:
% 1.22/1.50     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.22/1.50       ( ![D:$i]:
% 1.22/1.50         ( ( r2_hidden @ D @ C ) <=>
% 1.22/1.50           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.22/1.50  thf('32', plain,
% 1.22/1.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.50         (~ (r2_hidden @ X4 @ X3)
% 1.22/1.50          | (r2_hidden @ X4 @ X1)
% 1.22/1.50          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.22/1.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.22/1.50  thf('33', plain,
% 1.22/1.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.22/1.50         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.22/1.50      inference('simplify', [status(thm)], ['32'])).
% 1.22/1.50  thf('34', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.22/1.50          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.22/1.50      inference('sup-', [status(thm)], ['31', '33'])).
% 1.22/1.50  thf('35', plain,
% 1.22/1.50      (![X10 : $i]:
% 1.22/1.50         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.22/1.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.22/1.50  thf('36', plain,
% 1.22/1.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.22/1.50         (~ (r2_hidden @ X4 @ X3)
% 1.22/1.50          | (r2_hidden @ X4 @ X2)
% 1.22/1.50          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.22/1.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.22/1.50  thf('37', plain,
% 1.22/1.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.22/1.50         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.22/1.50      inference('simplify', [status(thm)], ['36'])).
% 1.22/1.50  thf('38', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.22/1.50          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.22/1.50      inference('sup-', [status(thm)], ['35', '37'])).
% 1.22/1.50  thf('39', plain,
% 1.22/1.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.22/1.50         (~ (r2_hidden @ X8 @ X6)
% 1.22/1.50          | ~ (r2_hidden @ X8 @ X9)
% 1.22/1.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.22/1.50  thf('40', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.22/1.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.22/1.50          | ~ (r1_xboole_0 @ X0 @ X2)
% 1.22/1.50          | ~ (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X2))),
% 1.22/1.50      inference('sup-', [status(thm)], ['38', '39'])).
% 1.22/1.50  thf('41', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0))
% 1.22/1.50          | ~ (r1_xboole_0 @ X1 @ X0)
% 1.22/1.50          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 1.22/1.50      inference('sup-', [status(thm)], ['34', '40'])).
% 1.22/1.50  thf('42', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (~ (r1_xboole_0 @ X1 @ X0) | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 1.22/1.50      inference('simplify', [status(thm)], ['41'])).
% 1.22/1.50  thf('43', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         ((r2_hidden @ X0 @ X1)
% 1.22/1.50          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 1.22/1.50      inference('sup-', [status(thm)], ['30', '42'])).
% 1.22/1.50  thf(t100_xboole_1, axiom,
% 1.22/1.50    (![A:$i,B:$i]:
% 1.22/1.50     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.22/1.50  thf('44', plain,
% 1.22/1.50      (![X11 : $i, X12 : $i]:
% 1.22/1.50         ((k4_xboole_0 @ X11 @ X12)
% 1.22/1.50           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.22/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.50  thf('45', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 1.22/1.50            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 1.22/1.50          | (r2_hidden @ X1 @ X0))),
% 1.22/1.50      inference('sup+', [status(thm)], ['43', '44'])).
% 1.22/1.50  thf(t3_boole, axiom,
% 1.22/1.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.22/1.50  thf('46', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.22/1.50  thf('47', plain,
% 1.22/1.50      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 1.22/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.22/1.50  thf('48', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.22/1.50      inference('sup+', [status(thm)], ['46', '47'])).
% 1.22/1.50  thf('49', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.22/1.50          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.22/1.50      inference('sup-', [status(thm)], ['35', '37'])).
% 1.22/1.50  thf('50', plain,
% 1.22/1.50      (![X10 : $i]:
% 1.22/1.50         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.22/1.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.22/1.50  thf('51', plain,
% 1.22/1.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.22/1.50         (~ (r2_hidden @ X8 @ X6)
% 1.22/1.50          | ~ (r2_hidden @ X8 @ X9)
% 1.22/1.50          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.22/1.50  thf('52', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((X0) = (k1_xboole_0))
% 1.22/1.50          | ~ (r1_xboole_0 @ X0 @ X1)
% 1.22/1.50          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 1.22/1.50      inference('sup-', [status(thm)], ['50', '51'])).
% 1.22/1.50  thf('53', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.22/1.50          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.22/1.50          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.22/1.50      inference('sup-', [status(thm)], ['49', '52'])).
% 1.22/1.50  thf('54', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.22/1.50          | ((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 1.22/1.50      inference('simplify', [status(thm)], ['53'])).
% 1.22/1.50  thf('55', plain,
% 1.22/1.50      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.22/1.50      inference('sup-', [status(thm)], ['48', '54'])).
% 1.22/1.50  thf('56', plain,
% 1.22/1.50      (![X11 : $i, X12 : $i]:
% 1.22/1.50         ((k4_xboole_0 @ X11 @ X12)
% 1.22/1.50           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.22/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.50  thf('57', plain,
% 1.22/1.50      (![X0 : $i]:
% 1.22/1.50         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.50      inference('sup+', [status(thm)], ['55', '56'])).
% 1.22/1.50  thf('58', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 1.22/1.50      inference('cnf', [status(esa)], [t3_boole])).
% 1.22/1.50  thf('59', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.22/1.50      inference('sup+', [status(thm)], ['57', '58'])).
% 1.22/1.50  thf('60', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 1.22/1.50          | (r2_hidden @ X1 @ X0))),
% 1.22/1.50      inference('demod', [status(thm)], ['45', '59'])).
% 1.22/1.50  thf('61', plain,
% 1.22/1.50      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 1.22/1.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.22/1.50  thf('62', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (~ (r1_xboole_0 @ X1 @ X0) | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 1.22/1.50      inference('simplify', [status(thm)], ['41'])).
% 1.22/1.50  thf('63', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.22/1.50      inference('sup-', [status(thm)], ['61', '62'])).
% 1.22/1.50  thf('64', plain,
% 1.22/1.50      (![X11 : $i, X12 : $i]:
% 1.22/1.50         ((k4_xboole_0 @ X11 @ X12)
% 1.22/1.50           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 1.22/1.50      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.22/1.50  thf('65', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 1.22/1.50           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.22/1.50      inference('sup+', [status(thm)], ['63', '64'])).
% 1.22/1.50  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.22/1.50      inference('sup+', [status(thm)], ['57', '58'])).
% 1.22/1.50  thf('67', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.22/1.50      inference('demod', [status(thm)], ['65', '66'])).
% 1.22/1.50  thf('68', plain,
% 1.22/1.50      (![X0 : $i, X1 : $i]:
% 1.22/1.50         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 1.22/1.50          | (r2_hidden @ X0 @ X1))),
% 1.22/1.50      inference('sup+', [status(thm)], ['60', '67'])).
% 1.22/1.50  thf('69', plain,
% 1.22/1.50      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 1.22/1.50         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('split', [status(esa)], ['0'])).
% 1.22/1.50  thf('70', plain,
% 1.22/1.50      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 1.22/1.50         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('sup-', [status(thm)], ['68', '69'])).
% 1.22/1.50  thf('71', plain,
% 1.22/1.50      (((r2_hidden @ sk_B_1 @ sk_A))
% 1.22/1.50         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 1.22/1.50      inference('simplify', [status(thm)], ['70'])).
% 1.22/1.50  thf('72', plain,
% 1.22/1.50      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 1.22/1.50      inference('split', [status(esa)], ['3'])).
% 1.22/1.50  thf('73', plain,
% 1.22/1.50      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 1.22/1.50       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 1.22/1.50      inference('sup-', [status(thm)], ['71', '72'])).
% 1.22/1.50  thf('74', plain, ($false),
% 1.22/1.50      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '73'])).
% 1.22/1.50  
% 1.22/1.50  % SZS output end Refutation
% 1.22/1.50  
% 1.22/1.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
