%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aClOlv0YDn

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:52 EST 2020

% Result     : Theorem 2.37s
% Output     : Refutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 173 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  789 (1384 expanded)
%              Number of equality atoms :   74 ( 132 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X37 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X28 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( X14 != X15 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X15: $i] :
      ( r1_tarski @ X15 @ X15 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X50 ) @ X51 )
      | ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('19',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('42',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k4_xboole_0 @ X22 @ X23 ) )
      = ( k3_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('44',plain,(
    ! [X24: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('63',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
        = X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('67',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['35'])).

thf('70',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','40','41','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aClOlv0YDn
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.37/2.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.37/2.55  % Solved by: fo/fo7.sh
% 2.37/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.37/2.55  % done 2566 iterations in 2.066s
% 2.37/2.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.37/2.55  % SZS output start Refutation
% 2.37/2.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.37/2.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.37/2.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 2.37/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.37/2.55  thf(sk_B_type, type, sk_B: $i).
% 2.37/2.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.37/2.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.37/2.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.37/2.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.37/2.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.37/2.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.37/2.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.37/2.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.37/2.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.37/2.55  thf(t65_zfmisc_1, conjecture,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.37/2.55       ( ~( r2_hidden @ B @ A ) ) ))).
% 2.37/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.37/2.55    (~( ![A:$i,B:$i]:
% 2.37/2.55        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 2.37/2.55          ( ~( r2_hidden @ B @ A ) ) ) )),
% 2.37/2.55    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 2.37/2.55  thf('0', plain,
% 2.37/2.55      (((r2_hidden @ sk_B @ sk_A)
% 2.37/2.55        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf('1', plain,
% 2.37/2.55      (((r2_hidden @ sk_B @ sk_A)) | 
% 2.37/2.55       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 2.37/2.55      inference('split', [status(esa)], ['0'])).
% 2.37/2.55  thf('2', plain,
% 2.37/2.55      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 2.37/2.55      inference('split', [status(esa)], ['0'])).
% 2.37/2.55  thf(t70_enumset1, axiom,
% 2.37/2.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 2.37/2.55  thf('3', plain,
% 2.37/2.55      (![X41 : $i, X42 : $i]:
% 2.37/2.55         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 2.37/2.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 2.37/2.55  thf(d1_enumset1, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.37/2.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.37/2.55       ( ![E:$i]:
% 2.37/2.55         ( ( r2_hidden @ E @ D ) <=>
% 2.37/2.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 2.37/2.55  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 2.37/2.55  thf(zf_stmt_2, axiom,
% 2.37/2.55    (![E:$i,C:$i,B:$i,A:$i]:
% 2.37/2.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 2.37/2.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 2.37/2.55  thf(zf_stmt_3, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.37/2.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 2.37/2.55       ( ![E:$i]:
% 2.37/2.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 2.37/2.55  thf('4', plain,
% 2.37/2.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 2.37/2.55         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36)
% 2.37/2.55          | (r2_hidden @ X33 @ X37)
% 2.37/2.55          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.37/2.55  thf('5', plain,
% 2.37/2.55      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.37/2.55         ((r2_hidden @ X33 @ (k1_enumset1 @ X36 @ X35 @ X34))
% 2.37/2.55          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 2.37/2.55      inference('simplify', [status(thm)], ['4'])).
% 2.37/2.55  thf('6', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 2.37/2.55          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 2.37/2.55      inference('sup+', [status(thm)], ['3', '5'])).
% 2.37/2.55  thf('7', plain,
% 2.37/2.55      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 2.37/2.55         (((X29) != (X28)) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X28))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 2.37/2.55  thf('8', plain,
% 2.37/2.55      (![X28 : $i, X30 : $i, X31 : $i]:
% 2.37/2.55         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X28)),
% 2.37/2.55      inference('simplify', [status(thm)], ['7'])).
% 2.37/2.55  thf('9', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 2.37/2.55      inference('sup-', [status(thm)], ['6', '8'])).
% 2.37/2.55  thf(t69_enumset1, axiom,
% 2.37/2.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.37/2.55  thf('10', plain,
% 2.37/2.55      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 2.37/2.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 2.37/2.55  thf(d10_xboole_0, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.37/2.55  thf('11', plain,
% 2.37/2.55      (![X14 : $i, X15 : $i]: ((r1_tarski @ X14 @ X15) | ((X14) != (X15)))),
% 2.37/2.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.37/2.55  thf('12', plain, (![X15 : $i]: (r1_tarski @ X15 @ X15)),
% 2.37/2.55      inference('simplify', [status(thm)], ['11'])).
% 2.37/2.55  thf(t28_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.37/2.55  thf('13', plain,
% 2.37/2.55      (![X19 : $i, X20 : $i]:
% 2.37/2.55         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 2.37/2.55      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.37/2.55  thf('14', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.37/2.55      inference('sup-', [status(thm)], ['12', '13'])).
% 2.37/2.55  thf(l27_zfmisc_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.37/2.55  thf('15', plain,
% 2.37/2.55      (![X50 : $i, X51 : $i]:
% 2.37/2.55         ((r1_xboole_0 @ (k1_tarski @ X50) @ X51) | (r2_hidden @ X50 @ X51))),
% 2.37/2.55      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.37/2.55  thf(t83_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.37/2.55  thf('16', plain,
% 2.37/2.55      (![X25 : $i, X26 : $i]:
% 2.37/2.55         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 2.37/2.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.37/2.55  thf('17', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         ((r2_hidden @ X1 @ X0)
% 2.37/2.55          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['15', '16'])).
% 2.37/2.55  thf(t48_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.37/2.55  thf('18', plain,
% 2.37/2.55      (![X22 : $i, X23 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 2.37/2.55           = (k3_xboole_0 @ X22 @ X23))),
% 2.37/2.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.37/2.55  thf('19', plain,
% 2.37/2.55      (![X22 : $i, X23 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 2.37/2.55           = (k3_xboole_0 @ X22 @ X23))),
% 2.37/2.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.37/2.55  thf('20', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 2.37/2.55           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.37/2.55      inference('sup+', [status(thm)], ['18', '19'])).
% 2.37/2.55  thf(d5_xboole_0, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.37/2.55       ( ![D:$i]:
% 2.37/2.55         ( ( r2_hidden @ D @ C ) <=>
% 2.37/2.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.37/2.55  thf('21', plain,
% 2.37/2.55      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X12 @ X11)
% 2.37/2.55          | ~ (r2_hidden @ X12 @ X10)
% 2.37/2.55          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 2.37/2.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.37/2.55  thf('22', plain,
% 2.37/2.55      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X12 @ X10)
% 2.37/2.55          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.37/2.55      inference('simplify', [status(thm)], ['21'])).
% 2.37/2.55  thf('23', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 2.37/2.55          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['20', '22'])).
% 2.37/2.55  thf('24', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X2 @ 
% 2.37/2.55             (k3_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 2.37/2.55          | (r2_hidden @ X0 @ X1)
% 2.37/2.55          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['17', '23'])).
% 2.37/2.55  thf('25', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.37/2.55      inference('sup-', [status(thm)], ['12', '13'])).
% 2.37/2.55  thf('26', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 2.37/2.55          | (r2_hidden @ X0 @ X1)
% 2.37/2.55          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.37/2.55      inference('demod', [status(thm)], ['24', '25'])).
% 2.37/2.55  thf(commutativity_k3_xboole_0, axiom,
% 2.37/2.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.37/2.55  thf('27', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.37/2.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.37/2.55  thf(d4_xboole_0, axiom,
% 2.37/2.55    (![A:$i,B:$i,C:$i]:
% 2.37/2.55     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 2.37/2.55       ( ![D:$i]:
% 2.37/2.55         ( ( r2_hidden @ D @ C ) <=>
% 2.37/2.55           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.37/2.55  thf('28', plain,
% 2.37/2.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X6 @ X5)
% 2.37/2.55          | (r2_hidden @ X6 @ X4)
% 2.37/2.55          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 2.37/2.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.37/2.55  thf('29', plain,
% 2.37/2.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.37/2.55         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.37/2.55      inference('simplify', [status(thm)], ['28'])).
% 2.37/2.55  thf('30', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.37/2.55      inference('sup-', [status(thm)], ['27', '29'])).
% 2.37/2.55  thf('31', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 2.37/2.55          | (r2_hidden @ X0 @ X1))),
% 2.37/2.55      inference('clc', [status(thm)], ['26', '30'])).
% 2.37/2.55  thf('32', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 2.37/2.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['14', '31'])).
% 2.37/2.55  thf('33', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 2.37/2.55          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['10', '32'])).
% 2.37/2.55  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 2.37/2.55      inference('sup-', [status(thm)], ['9', '33'])).
% 2.37/2.55  thf('35', plain,
% 2.37/2.55      ((~ (r2_hidden @ sk_B @ sk_A)
% 2.37/2.55        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 2.37/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.37/2.55  thf('36', plain,
% 2.37/2.55      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 2.37/2.55         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 2.37/2.55      inference('split', [status(esa)], ['35'])).
% 2.37/2.55  thf('37', plain,
% 2.37/2.55      (![X9 : $i, X10 : $i, X12 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X12 @ X10)
% 2.37/2.55          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 2.37/2.55      inference('simplify', [status(thm)], ['21'])).
% 2.37/2.55  thf('38', plain,
% 2.37/2.55      ((![X0 : $i]:
% 2.37/2.55          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 2.37/2.55         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 2.37/2.55      inference('sup-', [status(thm)], ['36', '37'])).
% 2.37/2.55  thf('39', plain,
% 2.37/2.55      ((~ (r2_hidden @ sk_B @ sk_A))
% 2.37/2.55         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 2.37/2.55      inference('sup-', [status(thm)], ['34', '38'])).
% 2.37/2.55  thf('40', plain,
% 2.37/2.55      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 2.37/2.55       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['2', '39'])).
% 2.37/2.55  thf('41', plain,
% 2.37/2.55      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 2.37/2.55       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 2.37/2.55      inference('split', [status(esa)], ['35'])).
% 2.37/2.55  thf('42', plain,
% 2.37/2.55      (![X3 : $i, X4 : $i, X7 : $i]:
% 2.37/2.55         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 2.37/2.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 2.37/2.55          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 2.37/2.55      inference('cnf', [status(esa)], [d4_xboole_0])).
% 2.37/2.55  thf('43', plain,
% 2.37/2.55      (![X22 : $i, X23 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X22 @ (k4_xboole_0 @ X22 @ X23))
% 2.37/2.55           = (k3_xboole_0 @ X22 @ X23))),
% 2.37/2.55      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.37/2.55  thf(t4_boole, axiom,
% 2.37/2.55    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.37/2.55  thf('44', plain,
% 2.37/2.55      (![X24 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X24) = (k1_xboole_0))),
% 2.37/2.55      inference('cnf', [status(esa)], [t4_boole])).
% 2.37/2.55  thf('45', plain,
% 2.37/2.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['43', '44'])).
% 2.37/2.55  thf('46', plain,
% 2.37/2.55      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.37/2.55         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 2.37/2.55      inference('simplify', [status(thm)], ['28'])).
% 2.37/2.55  thf('47', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 2.37/2.55      inference('sup-', [status(thm)], ['45', '46'])).
% 2.37/2.55  thf('48', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 2.37/2.55          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 2.37/2.55          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X2))),
% 2.37/2.55      inference('sup-', [status(thm)], ['42', '47'])).
% 2.37/2.55  thf('49', plain,
% 2.37/2.55      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['43', '44'])).
% 2.37/2.55  thf('50', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.37/2.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.37/2.55  thf('51', plain,
% 2.37/2.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['49', '50'])).
% 2.37/2.55  thf('52', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 2.37/2.55          | ((X1) = (k1_xboole_0))
% 2.37/2.55          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X2))),
% 2.37/2.55      inference('demod', [status(thm)], ['48', '51'])).
% 2.37/2.55  thf('53', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ X1) @ X0)
% 2.37/2.55          | ((X0) = (k1_xboole_0)))),
% 2.37/2.55      inference('condensation', [status(thm)], ['52'])).
% 2.37/2.55  thf('54', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.37/2.55         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 2.37/2.55          | (r2_hidden @ X0 @ X1))),
% 2.37/2.55      inference('clc', [status(thm)], ['26', '30'])).
% 2.37/2.55  thf('55', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         (((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 2.37/2.55          | (r2_hidden @ X1 @ X0))),
% 2.37/2.55      inference('sup-', [status(thm)], ['53', '54'])).
% 2.37/2.55  thf('56', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.37/2.55      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.37/2.55  thf(t100_xboole_1, axiom,
% 2.37/2.55    (![A:$i,B:$i]:
% 2.37/2.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.37/2.55  thf('57', plain,
% 2.37/2.55      (![X17 : $i, X18 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X17 @ X18)
% 2.37/2.55           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 2.37/2.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.37/2.55  thf('58', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X0 @ X1)
% 2.37/2.55           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.37/2.55      inference('sup+', [status(thm)], ['56', '57'])).
% 2.37/2.55  thf('59', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1))
% 2.37/2.55            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 2.37/2.55          | (r2_hidden @ X1 @ X0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['55', '58'])).
% 2.37/2.55  thf('60', plain,
% 2.37/2.55      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['49', '50'])).
% 2.37/2.55  thf('61', plain,
% 2.37/2.55      (![X17 : $i, X18 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X17 @ X18)
% 2.37/2.55           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 2.37/2.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 2.37/2.55  thf('62', plain,
% 2.37/2.55      (![X0 : $i]:
% 2.37/2.55         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['60', '61'])).
% 2.37/2.55  thf(t3_boole, axiom,
% 2.37/2.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.37/2.55  thf('63', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 2.37/2.55      inference('cnf', [status(esa)], [t3_boole])).
% 2.37/2.55  thf('64', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.37/2.55      inference('sup+', [status(thm)], ['62', '63'])).
% 2.37/2.55  thf('65', plain,
% 2.37/2.55      (![X0 : $i, X1 : $i]:
% 2.37/2.55         (((k4_xboole_0 @ X0 @ (k1_tarski @ X1)) = (X0))
% 2.37/2.55          | (r2_hidden @ X1 @ X0))),
% 2.37/2.55      inference('demod', [status(thm)], ['59', '64'])).
% 2.37/2.55  thf('66', plain,
% 2.37/2.55      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 2.37/2.55         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 2.37/2.55      inference('split', [status(esa)], ['0'])).
% 2.37/2.55  thf('67', plain,
% 2.37/2.55      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 2.37/2.55         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 2.37/2.55      inference('sup-', [status(thm)], ['65', '66'])).
% 2.37/2.55  thf('68', plain,
% 2.37/2.55      (((r2_hidden @ sk_B @ sk_A))
% 2.37/2.55         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 2.37/2.55      inference('simplify', [status(thm)], ['67'])).
% 2.37/2.55  thf('69', plain,
% 2.37/2.55      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 2.37/2.55      inference('split', [status(esa)], ['35'])).
% 2.37/2.55  thf('70', plain,
% 2.37/2.55      (((r2_hidden @ sk_B @ sk_A)) | 
% 2.37/2.55       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 2.37/2.55      inference('sup-', [status(thm)], ['68', '69'])).
% 2.37/2.55  thf('71', plain, ($false),
% 2.37/2.55      inference('sat_resolution*', [status(thm)], ['1', '40', '41', '70'])).
% 2.37/2.55  
% 2.37/2.55  % SZS output end Refutation
% 2.37/2.55  
% 2.37/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
