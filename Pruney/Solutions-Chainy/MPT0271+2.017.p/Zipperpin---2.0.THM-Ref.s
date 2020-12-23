%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PDLgsyQYth

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:23 EST 2020

% Result     : Theorem 2.04s
% Output     : Refutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 596 expanded)
%              Number of leaves         :   38 ( 194 expanded)
%              Depth                    :   18
%              Number of atoms          : 1497 (4770 expanded)
%              Number of equality atoms :  162 ( 502 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X44 != X43 )
      | ( r2_hidden @ X44 @ X45 )
      | ( X45
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X43: $i] :
      ( r2_hidden @ X43 @ ( k1_tarski @ X43 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ( r2_hidden @ X10 @ X12 )
      | ( r2_hidden @ X10 @ X13 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      | ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k3_xboole_0 @ X26 @ ( k4_xboole_0 @ X27 @ X28 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X26 @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('21',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ( X13
       != ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ X3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','26'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('28',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_xboole_0 @ X36 @ X37 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X36 @ X37 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X38: $i,X40: $i] :
      ( ( r1_xboole_0 @ X38 @ X40 )
      | ( ( k4_xboole_0 @ X38 @ X40 )
       != X38 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ X39 )
        = X38 )
      | ~ ( r1_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('38',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ sk_A ) ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
          = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf(t76_enumset1,axiom,(
    ! [A: $i] :
      ( ( k1_enumset1 @ A @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('41',plain,(
    ! [X55: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X55 )
      = ( k1_tarski @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('42',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('43',plain,(
    ! [X55: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X55 )
      = ( k1_tarski @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('44',plain,(
    ! [X43: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ X46 @ X45 )
      | ( X46 = X43 )
      | ( X45
       != ( k1_tarski @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('45',plain,(
    ! [X43: $i,X46: $i] :
      ( ( X46 = X43 )
      | ~ ( r2_hidden @ X46 @ ( k1_tarski @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_enumset1 @ X0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('48',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( k2_enumset1 @ X52 @ X52 @ X53 @ X54 )
      = ( k1_enumset1 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t45_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('49',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_xboole_0 @ ( k2_tarski @ X48 @ X49 ) @ ( k2_tarski @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf(t50_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf('50',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X59 @ X60 ) @ X61 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t50_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k2_enumset1 @ X3 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
        | ( ( k1_tarski @ sk_A )
          = k1_xboole_0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','54','55'])).

thf('57',plain,(
    ! [X55: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X55 )
      = ( k1_tarski @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['10'])).

thf('65',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('66',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['10'])).

thf(t48_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r2_hidden @ C @ B ) )
     => ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
        = B ) ) )).

thf('67',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( r2_hidden @ X56 @ X57 )
      | ~ ( r2_hidden @ X58 @ X57 )
      | ( ( k2_xboole_0 @ ( k2_tarski @ X56 @ X58 ) @ X57 )
        = X57 ) ) ),
    inference(cnf,[status(esa)],[t48_zfmisc_1])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) @ sk_B_1 )
          = sk_B_1 )
        | ~ ( r2_hidden @ X0 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 )
      = sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('70',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t24_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ) )).

thf('71',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ ( k2_xboole_0 @ X23 @ X24 ) @ ( k2_xboole_0 @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t24_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['24'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','77','78'])).

thf('80',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['69','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('82',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k3_xboole_0 @ sk_B_1 @ ( k2_tarski @ sk_A @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('86',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ X39 )
        = X38 )
      | ~ ( r1_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('90',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k4_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X35 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X33 @ X34 ) @ ( k3_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','94'])).

thf('96',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_A ) @ ( k2_tarski @ sk_A @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['83','95'])).

thf('97',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( k2_enumset1 @ X48 @ X49 @ X50 @ X51 )
      = ( k2_xboole_0 @ ( k2_tarski @ X48 @ X49 ) @ ( k2_tarski @ X50 @ X51 ) ) ) ),
    inference(cnf,[status(esa)],[t45_enumset1])).

thf('98',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( k2_enumset1 @ X52 @ X52 @ X53 @ X54 )
      = ( k1_enumset1 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('99',plain,(
    ! [X55: $i] :
      ( ( k1_enumset1 @ X55 @ X55 @ X55 )
      = ( k1_tarski @ X55 ) ) ),
    inference(cnf,[status(esa)],[t76_enumset1])).

thf('100',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,
    ( ( ( k2_tarski @ sk_A @ sk_A )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('102',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['82','100','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('104',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X32 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X30 @ X31 ) @ ( k3_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('106',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k3_xboole_0 @ X30 @ ( k4_xboole_0 @ X31 @ X32 ) )
      = ( k3_xboole_0 @ X31 @ ( k4_xboole_0 @ X30 @ ( k3_xboole_0 @ X30 @ X32 ) ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('107',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['72','77','78'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['106','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','114'])).

thf('116',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['102','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('118',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X16: $i] :
      ( ( k2_xboole_0 @ X16 @ X16 )
      = X16 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('123',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('124',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X41 @ X42 ) @ X42 )
        = X41 )
      | ~ ( r1_xboole_0 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf('127',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X22: $i] :
      ( ( k2_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('138',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['122','141'])).

thf('143',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['116','121','142'])).

thf('144',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PDLgsyQYth
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.04/2.24  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.04/2.24  % Solved by: fo/fo7.sh
% 2.04/2.24  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.04/2.24  % done 2717 iterations in 1.788s
% 2.04/2.24  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.04/2.24  % SZS output start Refutation
% 2.04/2.24  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 2.04/2.24  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.04/2.24  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.04/2.24  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 2.04/2.24  thf(sk_B_type, type, sk_B: $i > $i).
% 2.04/2.24  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.04/2.24  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 2.04/2.24  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.04/2.24  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.04/2.24  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.04/2.24  thf(sk_A_type, type, sk_A: $i).
% 2.04/2.24  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.04/2.24  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.04/2.24  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.04/2.24  thf(t68_zfmisc_1, conjecture,
% 2.04/2.24    (![A:$i,B:$i]:
% 2.04/2.24     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 2.04/2.24       ( r2_hidden @ A @ B ) ))).
% 2.04/2.24  thf(zf_stmt_0, negated_conjecture,
% 2.04/2.24    (~( ![A:$i,B:$i]:
% 2.04/2.24        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 2.04/2.24          ( r2_hidden @ A @ B ) ) )),
% 2.04/2.24    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 2.04/2.24  thf('0', plain,
% 2.04/2.24      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 2.04/2.24        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_xboole_0)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('1', plain,
% 2.04/2.24      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 2.04/2.24       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 2.04/2.24      inference('split', [status(esa)], ['0'])).
% 2.04/2.24  thf(d1_tarski, axiom,
% 2.04/2.24    (![A:$i,B:$i]:
% 2.04/2.24     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 2.04/2.24       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 2.04/2.24  thf('2', plain,
% 2.04/2.24      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.04/2.24         (((X44) != (X43))
% 2.04/2.24          | (r2_hidden @ X44 @ X45)
% 2.04/2.24          | ((X45) != (k1_tarski @ X43)))),
% 2.04/2.24      inference('cnf', [status(esa)], [d1_tarski])).
% 2.04/2.24  thf('3', plain, (![X43 : $i]: (r2_hidden @ X43 @ (k1_tarski @ X43))),
% 2.04/2.24      inference('simplify', [status(thm)], ['2'])).
% 2.04/2.24  thf(d3_xboole_0, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 2.04/2.24       ( ![D:$i]:
% 2.04/2.24         ( ( r2_hidden @ D @ C ) <=>
% 2.04/2.24           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 2.04/2.24  thf('4', plain,
% 2.04/2.24      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X4 @ X5)
% 2.04/2.24          | (r2_hidden @ X4 @ X6)
% 2.04/2.24          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 2.04/2.24      inference('cnf', [status(esa)], [d3_xboole_0])).
% 2.04/2.24  thf('5', plain,
% 2.04/2.24      (![X4 : $i, X5 : $i, X7 : $i]:
% 2.04/2.24         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 2.04/2.24      inference('simplify', [status(thm)], ['4'])).
% 2.04/2.24  thf('6', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['3', '5'])).
% 2.04/2.24  thf(d5_xboole_0, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.04/2.24       ( ![D:$i]:
% 2.04/2.24         ( ( r2_hidden @ D @ C ) <=>
% 2.04/2.24           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.04/2.24  thf('7', plain,
% 2.04/2.24      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X10 @ X11)
% 2.04/2.24          | (r2_hidden @ X10 @ X12)
% 2.04/2.24          | (r2_hidden @ X10 @ X13)
% 2.04/2.24          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 2.04/2.24      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.04/2.24  thf('8', plain,
% 2.04/2.24      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.04/2.24         ((r2_hidden @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 2.04/2.24          | (r2_hidden @ X10 @ X12)
% 2.04/2.24          | ~ (r2_hidden @ X10 @ X11))),
% 2.04/2.24      inference('simplify', [status(thm)], ['7'])).
% 2.04/2.24  thf('9', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((r2_hidden @ X0 @ X2)
% 2.04/2.24          | (r2_hidden @ X0 @ 
% 2.04/2.24             (k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['6', '8'])).
% 2.04/2.24  thf('10', plain,
% 2.04/2.24      (((r2_hidden @ sk_A @ sk_B_1)
% 2.04/2.24        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 2.04/2.24      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.04/2.24  thf('11', plain,
% 2.04/2.24      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('split', [status(esa)], ['10'])).
% 2.04/2.24  thf(commutativity_k3_xboole_0, axiom,
% 2.04/2.24    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.04/2.24  thf('12', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.24  thf(t49_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.04/2.24       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 2.04/2.24  thf('13', plain,
% 2.04/2.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ X28))),
% 2.04/2.24      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.04/2.24  thf('14', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.04/2.24      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.24  thf('15', plain,
% 2.04/2.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ X28))),
% 2.04/2.24      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.04/2.24  thf('16', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ X0))
% 2.04/2.24           = (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['14', '15'])).
% 2.04/2.24  thf('17', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 2.04/2.24            = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1))))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('sup+', [status(thm)], ['11', '16'])).
% 2.04/2.24  thf(t7_xboole_0, axiom,
% 2.04/2.24    (![A:$i]:
% 2.04/2.24     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.04/2.24          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.04/2.24  thf('18', plain,
% 2.04/2.24      (![X19 : $i]:
% 2.04/2.24         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 2.04/2.24      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.04/2.24  thf(t4_boole, axiom,
% 2.04/2.24    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.04/2.24  thf('19', plain,
% 2.04/2.24      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 2.04/2.24      inference('cnf', [status(esa)], [t4_boole])).
% 2.04/2.24  thf('20', plain,
% 2.04/2.24      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X26 @ (k4_xboole_0 @ X27 @ X28))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X26 @ X27) @ X28))),
% 2.04/2.24      inference('cnf', [status(esa)], [t49_xboole_1])).
% 2.04/2.24  thf('21', plain,
% 2.04/2.24      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X14 @ X13)
% 2.04/2.24          | ~ (r2_hidden @ X14 @ X12)
% 2.04/2.24          | ((X13) != (k4_xboole_0 @ X11 @ X12)))),
% 2.04/2.24      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.04/2.24  thf('22', plain,
% 2.04/2.24      (![X11 : $i, X12 : $i, X14 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X14 @ X12)
% 2.04/2.24          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 2.04/2.24      inference('simplify', [status(thm)], ['21'])).
% 2.04/2.24  thf('23', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 2.04/2.24          | ~ (r2_hidden @ X3 @ X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['20', '22'])).
% 2.04/2.24  thf('24', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 2.04/2.24          | ~ (r2_hidden @ X2 @ X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['19', '23'])).
% 2.04/2.24  thf('25', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.04/2.24      inference('condensation', [status(thm)], ['24'])).
% 2.04/2.24  thf('26', plain,
% 2.04/2.24      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['18', '25'])).
% 2.04/2.24  thf('27', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          ((k1_xboole_0)
% 2.04/2.24            = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1))))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('demod', [status(thm)], ['17', '26'])).
% 2.04/2.24  thf(t75_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i]:
% 2.04/2.24     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.04/2.24          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 2.04/2.24  thf('28', plain,
% 2.04/2.24      (![X36 : $i, X37 : $i]:
% 2.04/2.24         ((r1_xboole_0 @ X36 @ X37)
% 2.04/2.24          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X36 @ X37) @ X37))),
% 2.04/2.24      inference('cnf', [status(esa)], [t75_xboole_1])).
% 2.04/2.24  thf('29', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          (~ (r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.24           | (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1))))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['27', '28'])).
% 2.04/2.24  thf('30', plain,
% 2.04/2.24      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 2.04/2.24      inference('cnf', [status(esa)], [t4_boole])).
% 2.04/2.24  thf(t83_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i]:
% 2.04/2.24     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.04/2.24  thf('31', plain,
% 2.04/2.24      (![X38 : $i, X40 : $i]:
% 2.04/2.24         ((r1_xboole_0 @ X38 @ X40) | ((k4_xboole_0 @ X38 @ X40) != (X38)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.04/2.24  thf('32', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['30', '31'])).
% 2.04/2.24  thf('33', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.04/2.24      inference('simplify', [status(thm)], ['32'])).
% 2.04/2.24  thf('34', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          (r1_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1)))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('demod', [status(thm)], ['29', '33'])).
% 2.04/2.24  thf('35', plain,
% 2.04/2.24      (![X38 : $i, X39 : $i]:
% 2.04/2.24         (((k4_xboole_0 @ X38 @ X39) = (X38)) | ~ (r1_xboole_0 @ X38 @ X39))),
% 2.04/2.24      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.04/2.24  thf('36', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.24            = (k1_tarski @ sk_A)))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['34', '35'])).
% 2.04/2.24  thf('37', plain,
% 2.04/2.24      (![X19 : $i]:
% 2.04/2.24         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 2.04/2.24      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.04/2.24  thf('38', plain,
% 2.04/2.24      (![X11 : $i, X12 : $i, X14 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X14 @ X12)
% 2.04/2.24          | ~ (r2_hidden @ X14 @ (k4_xboole_0 @ X11 @ X12)))),
% 2.04/2.24      inference('simplify', [status(thm)], ['21'])).
% 2.04/2.24  thf('39', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 2.04/2.24          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['37', '38'])).
% 2.04/2.24  thf('40', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          (~ (r2_hidden @ (sk_B @ (k1_tarski @ sk_A)) @ 
% 2.04/2.24              (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.24           | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.24               = (k1_xboole_0))))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['36', '39'])).
% 2.04/2.24  thf(t76_enumset1, axiom,
% 2.04/2.24    (![A:$i]: ( ( k1_enumset1 @ A @ A @ A ) = ( k1_tarski @ A ) ))).
% 2.04/2.24  thf('41', plain,
% 2.04/2.24      (![X55 : $i]: ((k1_enumset1 @ X55 @ X55 @ X55) = (k1_tarski @ X55))),
% 2.04/2.24      inference('cnf', [status(esa)], [t76_enumset1])).
% 2.04/2.24  thf('42', plain,
% 2.04/2.24      (![X19 : $i]:
% 2.04/2.24         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 2.04/2.24      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.04/2.24  thf('43', plain,
% 2.04/2.24      (![X55 : $i]: ((k1_enumset1 @ X55 @ X55 @ X55) = (k1_tarski @ X55))),
% 2.04/2.24      inference('cnf', [status(esa)], [t76_enumset1])).
% 2.04/2.24  thf('44', plain,
% 2.04/2.24      (![X43 : $i, X45 : $i, X46 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X46 @ X45)
% 2.04/2.24          | ((X46) = (X43))
% 2.04/2.24          | ((X45) != (k1_tarski @ X43)))),
% 2.04/2.24      inference('cnf', [status(esa)], [d1_tarski])).
% 2.04/2.24  thf('45', plain,
% 2.04/2.24      (![X43 : $i, X46 : $i]:
% 2.04/2.24         (((X46) = (X43)) | ~ (r2_hidden @ X46 @ (k1_tarski @ X43)))),
% 2.04/2.24      inference('simplify', [status(thm)], ['44'])).
% 2.04/2.24  thf('46', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X1 @ (k1_enumset1 @ X0 @ X0 @ X0)) | ((X1) = (X0)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['43', '45'])).
% 2.04/2.24  thf('47', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         (((k1_enumset1 @ X0 @ X0 @ X0) = (k1_xboole_0))
% 2.04/2.24          | ((sk_B @ (k1_enumset1 @ X0 @ X0 @ X0)) = (X0)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['42', '46'])).
% 2.04/2.24  thf(t71_enumset1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 2.04/2.24  thf('48', plain,
% 2.04/2.24      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.04/2.24         ((k2_enumset1 @ X52 @ X52 @ X53 @ X54)
% 2.04/2.24           = (k1_enumset1 @ X52 @ X53 @ X54))),
% 2.04/2.24      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.04/2.24  thf(t45_enumset1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i,D:$i]:
% 2.04/2.24     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 2.04/2.24       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 2.04/2.24  thf('49', plain,
% 2.04/2.24      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.04/2.24         ((k2_enumset1 @ X48 @ X49 @ X50 @ X51)
% 2.04/2.24           = (k2_xboole_0 @ (k2_tarski @ X48 @ X49) @ (k2_tarski @ X50 @ X51)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t45_enumset1])).
% 2.04/2.24  thf(t50_zfmisc_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 2.04/2.24  thf('50', plain,
% 2.04/2.24      (![X59 : $i, X60 : $i, X61 : $i]:
% 2.04/2.24         ((k2_xboole_0 @ (k2_tarski @ X59 @ X60) @ X61) != (k1_xboole_0))),
% 2.04/2.24      inference('cnf', [status(esa)], [t50_zfmisc_1])).
% 2.04/2.24  thf('51', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.04/2.24         ((k2_enumset1 @ X3 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['49', '50'])).
% 2.04/2.24  thf('52', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((k1_enumset1 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['48', '51'])).
% 2.04/2.24  thf('53', plain,
% 2.04/2.24      (![X0 : $i]: ((sk_B @ (k1_enumset1 @ X0 @ X0 @ X0)) = (X0))),
% 2.04/2.24      inference('simplify_reflect-', [status(thm)], ['47', '52'])).
% 2.04/2.24  thf('54', plain, (![X0 : $i]: ((sk_B @ (k1_tarski @ X0)) = (X0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['41', '53'])).
% 2.04/2.24  thf('55', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.24            = (k1_tarski @ sk_A)))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['34', '35'])).
% 2.04/2.24  thf('56', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1))
% 2.04/2.24           | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('demod', [status(thm)], ['40', '54', '55'])).
% 2.04/2.24  thf('57', plain,
% 2.04/2.24      (![X55 : $i]: ((k1_enumset1 @ X55 @ X55 @ X55) = (k1_tarski @ X55))),
% 2.04/2.24      inference('cnf', [status(esa)], [t76_enumset1])).
% 2.04/2.24  thf('58', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((k1_enumset1 @ X2 @ X1 @ X0) != (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['48', '51'])).
% 2.04/2.24  thf('59', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['57', '58'])).
% 2.04/2.24  thf('60', plain,
% 2.04/2.24      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 2.04/2.24  thf('61', plain,
% 2.04/2.24      (((r2_hidden @ sk_A @ sk_B_1))
% 2.04/2.24         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('sup-', [status(thm)], ['9', '60'])).
% 2.04/2.24  thf('62', plain,
% 2.04/2.24      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('split', [status(esa)], ['0'])).
% 2.04/2.24  thf('63', plain,
% 2.04/2.24      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 2.04/2.24       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['61', '62'])).
% 2.04/2.24  thf('64', plain,
% 2.04/2.24      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 2.04/2.24       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 2.04/2.24      inference('split', [status(esa)], ['10'])).
% 2.04/2.24  thf('65', plain,
% 2.04/2.24      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('split', [status(esa)], ['10'])).
% 2.04/2.24  thf('66', plain,
% 2.04/2.24      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('split', [status(esa)], ['10'])).
% 2.04/2.24  thf(t48_zfmisc_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( ( r2_hidden @ A @ B ) & ( r2_hidden @ C @ B ) ) =>
% 2.04/2.24       ( ( k2_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( B ) ) ))).
% 2.04/2.24  thf('67', plain,
% 2.04/2.24      (![X56 : $i, X57 : $i, X58 : $i]:
% 2.04/2.24         (~ (r2_hidden @ X56 @ X57)
% 2.04/2.24          | ~ (r2_hidden @ X58 @ X57)
% 2.04/2.24          | ((k2_xboole_0 @ (k2_tarski @ X56 @ X58) @ X57) = (X57)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t48_zfmisc_1])).
% 2.04/2.24  thf('68', plain,
% 2.04/2.24      ((![X0 : $i]:
% 2.04/2.24          (((k2_xboole_0 @ (k2_tarski @ sk_A @ X0) @ sk_B_1) = (sk_B_1))
% 2.04/2.24           | ~ (r2_hidden @ X0 @ sk_B_1)))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['66', '67'])).
% 2.04/2.24  thf('69', plain,
% 2.04/2.24      ((((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1) = (sk_B_1)))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['65', '68'])).
% 2.04/2.24  thf(t1_boole, axiom,
% 2.04/2.24    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.04/2.24  thf('70', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 2.04/2.24      inference('cnf', [status(esa)], [t1_boole])).
% 2.04/2.24  thf(t24_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 2.04/2.24       ( k3_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ C ) ) ))).
% 2.04/2.24  thf('71', plain,
% 2.04/2.24      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.04/2.24         ((k2_xboole_0 @ X23 @ (k3_xboole_0 @ X24 @ X25))
% 2.04/2.24           = (k3_xboole_0 @ (k2_xboole_0 @ X23 @ X24) @ 
% 2.04/2.24              (k2_xboole_0 @ X23 @ X25)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t24_xboole_1])).
% 2.04/2.24  thf('72', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 2.04/2.24           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['70', '71'])).
% 2.04/2.24  thf('73', plain,
% 2.04/2.24      (![X19 : $i]:
% 2.04/2.24         (((X19) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X19) @ X19))),
% 2.04/2.24      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.04/2.24  thf('74', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.24  thf('75', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.04/2.24      inference('condensation', [status(thm)], ['24'])).
% 2.04/2.24  thf('76', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['74', '75'])).
% 2.04/2.24  thf('77', plain,
% 2.04/2.24      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['73', '76'])).
% 2.04/2.24  thf('78', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 2.04/2.24      inference('cnf', [status(esa)], [t1_boole])).
% 2.04/2.24  thf('79', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['72', '77', '78'])).
% 2.04/2.24  thf('80', plain,
% 2.04/2.24      ((((k2_tarski @ sk_A @ sk_A)
% 2.04/2.24          = (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ sk_B_1)))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['69', '79'])).
% 2.04/2.24  thf('81', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.24  thf('82', plain,
% 2.04/2.24      ((((k2_tarski @ sk_A @ sk_A)
% 2.04/2.24          = (k3_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_A))))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['80', '81'])).
% 2.04/2.24  thf('83', plain,
% 2.04/2.24      ((((k2_tarski @ sk_A @ sk_A)
% 2.04/2.24          = (k3_xboole_0 @ sk_B_1 @ (k2_tarski @ sk_A @ sk_A))))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['80', '81'])).
% 2.04/2.24  thf('84', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.24  thf('85', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.04/2.24      inference('simplify', [status(thm)], ['32'])).
% 2.04/2.24  thf(symmetry_r1_xboole_0, axiom,
% 2.04/2.24    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.04/2.24  thf('86', plain,
% 2.04/2.24      (![X17 : $i, X18 : $i]:
% 2.04/2.24         ((r1_xboole_0 @ X17 @ X18) | ~ (r1_xboole_0 @ X18 @ X17))),
% 2.04/2.24      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.04/2.24  thf('87', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.04/2.24      inference('sup-', [status(thm)], ['85', '86'])).
% 2.04/2.24  thf('88', plain,
% 2.04/2.24      (![X38 : $i, X39 : $i]:
% 2.04/2.24         (((k4_xboole_0 @ X38 @ X39) = (X38)) | ~ (r1_xboole_0 @ X38 @ X39))),
% 2.04/2.24      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.04/2.24  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['87', '88'])).
% 2.04/2.24  thf(t52_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.04/2.24       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.04/2.24  thf('90', plain,
% 2.04/2.24      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.04/2.24         ((k4_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X35))
% 2.04/2.24           = (k2_xboole_0 @ (k4_xboole_0 @ X33 @ X34) @ 
% 2.04/2.24              (k3_xboole_0 @ X33 @ X35)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t52_xboole_1])).
% 2.04/2.24  thf('91', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 2.04/2.24           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['89', '90'])).
% 2.04/2.24  thf('92', plain,
% 2.04/2.24      (![X29 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X29) = (k1_xboole_0))),
% 2.04/2.24      inference('cnf', [status(esa)], [t4_boole])).
% 2.04/2.24  thf('93', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['87', '88'])).
% 2.04/2.24  thf('94', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['91', '92', '93'])).
% 2.04/2.24  thf('95', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['84', '94'])).
% 2.04/2.24  thf('96', plain,
% 2.04/2.24      ((((k2_tarski @ sk_A @ sk_A)
% 2.04/2.24          = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_A) @ 
% 2.04/2.24             (k2_tarski @ sk_A @ sk_A))))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['83', '95'])).
% 2.04/2.24  thf('97', plain,
% 2.04/2.24      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.04/2.24         ((k2_enumset1 @ X48 @ X49 @ X50 @ X51)
% 2.04/2.24           = (k2_xboole_0 @ (k2_tarski @ X48 @ X49) @ (k2_tarski @ X50 @ X51)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t45_enumset1])).
% 2.04/2.24  thf('98', plain,
% 2.04/2.24      (![X52 : $i, X53 : $i, X54 : $i]:
% 2.04/2.24         ((k2_enumset1 @ X52 @ X52 @ X53 @ X54)
% 2.04/2.24           = (k1_enumset1 @ X52 @ X53 @ X54))),
% 2.04/2.24      inference('cnf', [status(esa)], [t71_enumset1])).
% 2.04/2.24  thf('99', plain,
% 2.04/2.24      (![X55 : $i]: ((k1_enumset1 @ X55 @ X55 @ X55) = (k1_tarski @ X55))),
% 2.04/2.24      inference('cnf', [status(esa)], [t76_enumset1])).
% 2.04/2.24  thf('100', plain,
% 2.04/2.24      ((((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_A)))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 2.04/2.24  thf('101', plain,
% 2.04/2.24      ((((k2_tarski @ sk_A @ sk_A) = (k1_tarski @ sk_A)))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 2.04/2.24  thf('102', plain,
% 2.04/2.24      ((((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A))))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['82', '100', '101'])).
% 2.04/2.24  thf('103', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.04/2.24  thf(t50_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i,C:$i]:
% 2.04/2.24     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 2.04/2.24       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 2.04/2.24  thf('104', plain,
% 2.04/2.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X32))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X30 @ X31) @ 
% 2.04/2.24              (k3_xboole_0 @ X30 @ X32)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t50_xboole_1])).
% 2.04/2.24  thf('105', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.04/2.24      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.24  thf('106', plain,
% 2.04/2.24      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X30 @ (k4_xboole_0 @ X31 @ X32))
% 2.04/2.24           = (k3_xboole_0 @ X31 @ 
% 2.04/2.24              (k4_xboole_0 @ X30 @ (k3_xboole_0 @ X30 @ X32))))),
% 2.04/2.24      inference('demod', [status(thm)], ['104', '105'])).
% 2.04/2.24  thf(idempotence_k2_xboole_0, axiom,
% 2.04/2.24    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 2.04/2.24  thf('107', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ X16) = (X16))),
% 2.04/2.24      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.04/2.24  thf('108', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['72', '77', '78'])).
% 2.04/2.24  thf('109', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['107', '108'])).
% 2.04/2.24  thf('110', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 2.04/2.24           = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 2.04/2.24      inference('sup+', [status(thm)], ['12', '13'])).
% 2.04/2.24  thf('111', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.04/2.24           = (k4_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('sup+', [status(thm)], ['109', '110'])).
% 2.04/2.24  thf('112', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 2.04/2.24           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['106', '111'])).
% 2.04/2.24  thf('113', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.04/2.24           = (k4_xboole_0 @ X0 @ X1))),
% 2.04/2.24      inference('sup+', [status(thm)], ['109', '110'])).
% 2.04/2.24  thf('114', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k4_xboole_0 @ X1 @ X0)
% 2.04/2.24           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.24      inference('demod', [status(thm)], ['112', '113'])).
% 2.04/2.24  thf('115', plain,
% 2.04/2.24      (![X0 : $i, X1 : $i]:
% 2.04/2.24         ((k4_xboole_0 @ X0 @ X1)
% 2.04/2.24           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['103', '114'])).
% 2.04/2.24  thf('116', plain,
% 2.04/2.24      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 2.04/2.24          = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['102', '115'])).
% 2.04/2.24  thf('117', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['107', '108'])).
% 2.04/2.24  thf(t101_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i]:
% 2.04/2.24     ( ( k5_xboole_0 @ A @ B ) =
% 2.04/2.24       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.04/2.24  thf('118', plain,
% 2.04/2.24      (![X20 : $i, X21 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ X20 @ X21)
% 2.04/2.24           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 2.04/2.24              (k3_xboole_0 @ X20 @ X21)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t101_xboole_1])).
% 2.04/2.24  thf('119', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ X0 @ X0)
% 2.04/2.24           = (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X0) @ X0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['117', '118'])).
% 2.04/2.24  thf('120', plain, (![X16 : $i]: ((k2_xboole_0 @ X16 @ X16) = (X16))),
% 2.04/2.24      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 2.04/2.24  thf('121', plain,
% 2.04/2.24      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.04/2.24      inference('demod', [status(thm)], ['119', '120'])).
% 2.04/2.24  thf('122', plain,
% 2.04/2.24      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.04/2.24      inference('demod', [status(thm)], ['119', '120'])).
% 2.04/2.24  thf('123', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.04/2.24      inference('simplify', [status(thm)], ['32'])).
% 2.04/2.24  thf(t88_xboole_1, axiom,
% 2.04/2.24    (![A:$i,B:$i]:
% 2.04/2.24     ( ( r1_xboole_0 @ A @ B ) =>
% 2.04/2.24       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 2.04/2.24  thf('124', plain,
% 2.04/2.24      (![X41 : $i, X42 : $i]:
% 2.04/2.24         (((k4_xboole_0 @ (k2_xboole_0 @ X41 @ X42) @ X42) = (X41))
% 2.04/2.24          | ~ (r1_xboole_0 @ X41 @ X42))),
% 2.04/2.24      inference('cnf', [status(esa)], [t88_xboole_1])).
% 2.04/2.24  thf('125', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['123', '124'])).
% 2.04/2.24  thf('126', plain,
% 2.04/2.24      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['73', '76'])).
% 2.04/2.24  thf('127', plain,
% 2.04/2.24      (![X20 : $i, X21 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ X20 @ X21)
% 2.04/2.24           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 2.04/2.24              (k3_xboole_0 @ X20 @ X21)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t101_xboole_1])).
% 2.04/2.24  thf('128', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 2.04/2.24           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['126', '127'])).
% 2.04/2.24  thf('129', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['87', '88'])).
% 2.04/2.24  thf('130', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.24      inference('demod', [status(thm)], ['128', '129'])).
% 2.04/2.24  thf('131', plain, (![X22 : $i]: ((k2_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 2.04/2.24      inference('cnf', [status(esa)], [t1_boole])).
% 2.04/2.24  thf('132', plain,
% 2.04/2.24      (![X20 : $i, X21 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ X20 @ X21)
% 2.04/2.24           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 2.04/2.24              (k3_xboole_0 @ X20 @ X21)))),
% 2.04/2.24      inference('cnf', [status(esa)], [t101_xboole_1])).
% 2.04/2.24  thf('133', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 2.04/2.24           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 2.04/2.24      inference('sup+', [status(thm)], ['131', '132'])).
% 2.04/2.24  thf('134', plain,
% 2.04/2.24      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['18', '25'])).
% 2.04/2.24  thf('135', plain,
% 2.04/2.24      (![X0 : $i]:
% 2.04/2.24         ((k5_xboole_0 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 2.04/2.24      inference('demod', [status(thm)], ['133', '134'])).
% 2.04/2.24  thf('136', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.24      inference('sup-', [status(thm)], ['87', '88'])).
% 2.04/2.24  thf('137', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['135', '136'])).
% 2.04/2.24  thf(commutativity_k5_xboole_0, axiom,
% 2.04/2.24    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 2.04/2.24  thf('138', plain,
% 2.04/2.24      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 2.04/2.24      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 2.04/2.24  thf('139', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['137', '138'])).
% 2.04/2.24  thf('140', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.04/2.24      inference('demod', [status(thm)], ['130', '139'])).
% 2.04/2.24  thf('141', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.04/2.24      inference('demod', [status(thm)], ['125', '140'])).
% 2.04/2.24  thf('142', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.04/2.24      inference('sup+', [status(thm)], ['122', '141'])).
% 2.04/2.24  thf('143', plain,
% 2.04/2.24      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))
% 2.04/2.24         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('demod', [status(thm)], ['116', '121', '142'])).
% 2.04/2.24  thf('144', plain,
% 2.04/2.24      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_xboole_0)))
% 2.04/2.24         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))))),
% 2.04/2.24      inference('split', [status(esa)], ['0'])).
% 2.04/2.24  thf('145', plain,
% 2.04/2.24      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.04/2.24         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0))) & 
% 2.04/2.24             ((r2_hidden @ sk_A @ sk_B_1)))),
% 2.04/2.24      inference('sup-', [status(thm)], ['143', '144'])).
% 2.04/2.24  thf('146', plain,
% 2.04/2.24      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 2.04/2.24       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_xboole_0)))),
% 2.04/2.24      inference('simplify', [status(thm)], ['145'])).
% 2.04/2.24  thf('147', plain, ($false),
% 2.04/2.24      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '146'])).
% 2.04/2.24  
% 2.04/2.24  % SZS output end Refutation
% 2.04/2.24  
% 2.04/2.25  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
