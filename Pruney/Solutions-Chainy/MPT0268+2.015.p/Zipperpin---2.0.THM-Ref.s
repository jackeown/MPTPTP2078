%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2zSSYOZMzS

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:54 EST 2020

% Result     : Theorem 4.11s
% Output     : Refutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 158 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   19
%              Number of atoms          :  934 (1360 expanded)
%              Number of equality atoms :   89 ( 134 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 )
      | ( r2_hidden @ X26 @ X30 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_hidden @ X26 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) )
      | ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X29 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X22 != X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X21: $i,X23: $i,X24: $i] :
      ~ ( zip_tseitin_0 @ X21 @ X23 @ X24 @ X21 ) ),
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
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 @ X24 @ X25 )
      | ( X22 = X23 )
      | ( X22 = X24 )
      | ( X22 = X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ X12 @ X9 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('14',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ X12 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('17',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('18',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ( X30
       != ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X27: $i,X28: $i,X29: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X27 @ X28 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_enumset1 @ X29 @ X28 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_B @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_B @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 )
      | ( ( sk_B @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 )
      | ( ( sk_B @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('28',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X20 )
      | ( ( k4_xboole_0 @ X18 @ X20 )
       != X18 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('32',plain,(
    ! [X33: $i] :
      ( ( k2_tarski @ X33 @ X33 )
      = ( k1_tarski @ X33 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('33',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( r2_hidden @ X12 @ X10 )
      | ( X11
       != ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['30','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X1 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','49'])).

thf('51',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['2','55'])).

thf('57',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('59',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('60',plain,(
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

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('62',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['60','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','63'])).

thf('65',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X14 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('66',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ X16 )
      = ( k5_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','75'])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('78',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( r2_hidden @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('81',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','56','57','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2zSSYOZMzS
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:06:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.11/4.36  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.11/4.36  % Solved by: fo/fo7.sh
% 4.11/4.36  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.11/4.36  % done 4428 iterations in 3.897s
% 4.11/4.36  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.11/4.36  % SZS output start Refutation
% 4.11/4.36  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 4.11/4.36  thf(sk_B_type, type, sk_B: $i > $i).
% 4.11/4.36  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.11/4.36  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 4.11/4.36  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.11/4.36  thf(sk_B_1_type, type, sk_B_1: $i).
% 4.11/4.36  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.11/4.36  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.11/4.36  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.11/4.36  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.11/4.36  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.11/4.36  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.11/4.36  thf(sk_A_type, type, sk_A: $i).
% 4.11/4.36  thf(t65_zfmisc_1, conjecture,
% 4.11/4.36    (![A:$i,B:$i]:
% 4.11/4.36     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 4.11/4.36       ( ~( r2_hidden @ B @ A ) ) ))).
% 4.11/4.36  thf(zf_stmt_0, negated_conjecture,
% 4.11/4.36    (~( ![A:$i,B:$i]:
% 4.11/4.36        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 4.11/4.36          ( ~( r2_hidden @ B @ A ) ) ) )),
% 4.11/4.36    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 4.11/4.36  thf('0', plain,
% 4.11/4.36      (((r2_hidden @ sk_B_1 @ sk_A)
% 4.11/4.36        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))),
% 4.11/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.36  thf('1', plain,
% 4.11/4.36      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 4.11/4.36       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 4.11/4.36      inference('split', [status(esa)], ['0'])).
% 4.11/4.36  thf('2', plain,
% 4.11/4.36      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 4.11/4.36      inference('split', [status(esa)], ['0'])).
% 4.11/4.36  thf(t70_enumset1, axiom,
% 4.11/4.36    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 4.11/4.36  thf('3', plain,
% 4.11/4.36      (![X34 : $i, X35 : $i]:
% 4.11/4.36         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 4.11/4.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.11/4.36  thf(d1_enumset1, axiom,
% 4.11/4.36    (![A:$i,B:$i,C:$i,D:$i]:
% 4.11/4.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.11/4.36       ( ![E:$i]:
% 4.11/4.36         ( ( r2_hidden @ E @ D ) <=>
% 4.11/4.36           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 4.11/4.36  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 4.11/4.36  thf(zf_stmt_2, axiom,
% 4.11/4.36    (![E:$i,C:$i,B:$i,A:$i]:
% 4.11/4.36     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 4.11/4.36       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 4.11/4.36  thf(zf_stmt_3, axiom,
% 4.11/4.36    (![A:$i,B:$i,C:$i,D:$i]:
% 4.11/4.36     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 4.11/4.36       ( ![E:$i]:
% 4.11/4.36         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 4.11/4.36  thf('4', plain,
% 4.11/4.36      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 4.11/4.36         ((zip_tseitin_0 @ X26 @ X27 @ X28 @ X29)
% 4.11/4.36          | (r2_hidden @ X26 @ X30)
% 4.11/4.36          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 4.11/4.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.11/4.36  thf('5', plain,
% 4.11/4.36      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 4.11/4.36         ((r2_hidden @ X26 @ (k1_enumset1 @ X29 @ X28 @ X27))
% 4.11/4.36          | (zip_tseitin_0 @ X26 @ X27 @ X28 @ X29))),
% 4.11/4.36      inference('simplify', [status(thm)], ['4'])).
% 4.11/4.36  thf('6', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.36         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.11/4.36          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 4.11/4.36      inference('sup+', [status(thm)], ['3', '5'])).
% 4.11/4.36  thf('7', plain,
% 4.11/4.36      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 4.11/4.36         (((X22) != (X21)) | ~ (zip_tseitin_0 @ X22 @ X23 @ X24 @ X21))),
% 4.11/4.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.11/4.36  thf('8', plain,
% 4.11/4.36      (![X21 : $i, X23 : $i, X24 : $i]:
% 4.11/4.36         ~ (zip_tseitin_0 @ X21 @ X23 @ X24 @ X21)),
% 4.11/4.36      inference('simplify', [status(thm)], ['7'])).
% 4.11/4.36  thf('9', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['6', '8'])).
% 4.11/4.36  thf(t69_enumset1, axiom,
% 4.11/4.36    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.11/4.36  thf('10', plain,
% 4.11/4.36      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 4.11/4.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.36  thf('11', plain,
% 4.11/4.36      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 4.11/4.36         ((zip_tseitin_0 @ X22 @ X23 @ X24 @ X25)
% 4.11/4.36          | ((X22) = (X23))
% 4.11/4.36          | ((X22) = (X24))
% 4.11/4.36          | ((X22) = (X25)))),
% 4.11/4.36      inference('cnf', [status(esa)], [zf_stmt_2])).
% 4.11/4.36  thf(t7_xboole_0, axiom,
% 4.11/4.36    (![A:$i]:
% 4.11/4.36     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.11/4.36          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 4.11/4.36  thf('12', plain,
% 4.11/4.36      (![X14 : $i]:
% 4.11/4.36         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 4.11/4.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.11/4.36  thf(d5_xboole_0, axiom,
% 4.11/4.36    (![A:$i,B:$i,C:$i]:
% 4.11/4.36     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.11/4.36       ( ![D:$i]:
% 4.11/4.36         ( ( r2_hidden @ D @ C ) <=>
% 4.11/4.36           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.11/4.36  thf('13', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X12 @ X11)
% 4.11/4.36          | (r2_hidden @ X12 @ X9)
% 4.11/4.36          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.11/4.36  thf('14', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.11/4.36         ((r2_hidden @ X12 @ X9)
% 4.11/4.36          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['13'])).
% 4.11/4.36  thf('15', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.11/4.36          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['12', '14'])).
% 4.11/4.36  thf('16', plain,
% 4.11/4.36      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 4.11/4.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.36  thf('17', plain,
% 4.11/4.36      (![X34 : $i, X35 : $i]:
% 4.11/4.36         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 4.11/4.36      inference('cnf', [status(esa)], [t70_enumset1])).
% 4.11/4.36  thf('18', plain,
% 4.11/4.36      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X31 @ X30)
% 4.11/4.36          | ~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 4.11/4.36          | ((X30) != (k1_enumset1 @ X29 @ X28 @ X27)))),
% 4.11/4.36      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.11/4.36  thf('19', plain,
% 4.11/4.36      (![X27 : $i, X28 : $i, X29 : $i, X31 : $i]:
% 4.11/4.36         (~ (zip_tseitin_0 @ X31 @ X27 @ X28 @ X29)
% 4.11/4.36          | ~ (r2_hidden @ X31 @ (k1_enumset1 @ X29 @ X28 @ X27)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['18'])).
% 4.11/4.36  thf('20', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 4.11/4.36          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['17', '19'])).
% 4.11/4.36  thf('21', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.36          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 4.11/4.36      inference('sup-', [status(thm)], ['16', '20'])).
% 4.11/4.36  thf('22', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 4.11/4.36          | ~ (zip_tseitin_0 @ 
% 4.11/4.36               (sk_B @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) @ X0 @ X0 @ X0))),
% 4.11/4.36      inference('sup-', [status(thm)], ['15', '21'])).
% 4.11/4.36  thf('23', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((sk_B @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0))
% 4.11/4.36          | ((sk_B @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0))
% 4.11/4.36          | ((sk_B @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0))
% 4.11/4.36          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['11', '22'])).
% 4.11/4.36  thf('24', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 4.11/4.36          | ((sk_B @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)) = (X0)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['23'])).
% 4.11/4.36  thf('25', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.11/4.36          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['12', '14'])).
% 4.11/4.36  thf('26', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 4.11/4.36          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 4.11/4.36          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 4.11/4.36      inference('sup+', [status(thm)], ['24', '25'])).
% 4.11/4.36  thf('27', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['26'])).
% 4.11/4.36  thf(t83_xboole_1, axiom,
% 4.11/4.36    (![A:$i,B:$i]:
% 4.11/4.36     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.11/4.36  thf('28', plain,
% 4.11/4.36      (![X18 : $i, X20 : $i]:
% 4.11/4.36         ((r1_xboole_0 @ X18 @ X20) | ((k4_xboole_0 @ X18 @ X20) != (X18)))),
% 4.11/4.36      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.11/4.36  thf('29', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k1_xboole_0) != (k1_tarski @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 4.11/4.36          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['27', '28'])).
% 4.11/4.36  thf('30', plain,
% 4.11/4.36      (![X14 : $i]:
% 4.11/4.36         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 4.11/4.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.11/4.36  thf('31', plain,
% 4.11/4.36      (![X14 : $i]:
% 4.11/4.36         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 4.11/4.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.11/4.36  thf('32', plain,
% 4.11/4.36      (![X33 : $i]: ((k2_tarski @ X33 @ X33) = (k1_tarski @ X33))),
% 4.11/4.36      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.11/4.36  thf(l27_zfmisc_1, axiom,
% 4.11/4.36    (![A:$i,B:$i]:
% 4.11/4.36     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 4.11/4.36  thf('33', plain,
% 4.11/4.36      (![X39 : $i, X40 : $i]:
% 4.11/4.36         ((r1_xboole_0 @ (k1_tarski @ X39) @ X40) | (r2_hidden @ X39 @ X40))),
% 4.11/4.36      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 4.11/4.36  thf('34', plain,
% 4.11/4.36      (![X18 : $i, X19 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 4.11/4.36      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.11/4.36  thf('35', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((r2_hidden @ X1 @ X0)
% 4.11/4.36          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['33', '34'])).
% 4.11/4.36  thf('36', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ X1))),
% 4.11/4.36      inference('sup+', [status(thm)], ['32', '35'])).
% 4.11/4.36  thf('37', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X12 @ X11)
% 4.11/4.36          | ~ (r2_hidden @ X12 @ X10)
% 4.11/4.36          | ((X11) != (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.11/4.36  thf('38', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X12 @ X10)
% 4.11/4.36          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['37'])).
% 4.11/4.36  thf('39', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ X1)
% 4.11/4.36          | ~ (r2_hidden @ X2 @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['36', '38'])).
% 4.11/4.36  thf('40', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k1_tarski @ X0) = (k1_xboole_0))
% 4.11/4.36          | ~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ X1)
% 4.11/4.36          | (r2_hidden @ X0 @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['31', '39'])).
% 4.11/4.36  thf('41', plain,
% 4.11/4.36      (![X0 : $i]:
% 4.11/4.36         (((k1_tarski @ X0) = (k1_xboole_0))
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 4.11/4.36          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['30', '40'])).
% 4.11/4.36  thf('42', plain,
% 4.11/4.36      (![X0 : $i]:
% 4.11/4.36         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 4.11/4.36          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['41'])).
% 4.11/4.36  thf('43', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 4.11/4.36      inference('clc', [status(thm)], ['29', '42'])).
% 4.11/4.36  thf('44', plain,
% 4.11/4.36      (![X18 : $i, X19 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 4.11/4.36      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.11/4.36  thf('45', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((r2_hidden @ X1 @ (k1_tarski @ X1))
% 4.11/4.36          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['43', '44'])).
% 4.11/4.36  thf('46', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X12 @ X10)
% 4.11/4.36          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['37'])).
% 4.11/4.36  thf('47', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 4.11/4.36          | ~ (r2_hidden @ X2 @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['45', '46'])).
% 4.11/4.36  thf('48', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 4.11/4.36      inference('condensation', [status(thm)], ['47'])).
% 4.11/4.36  thf('49', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['10', '48'])).
% 4.11/4.36  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.11/4.36      inference('sup-', [status(thm)], ['9', '49'])).
% 4.11/4.36  thf('51', plain,
% 4.11/4.36      ((~ (r2_hidden @ sk_B_1 @ sk_A)
% 4.11/4.36        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 4.11/4.36      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.36  thf('52', plain,
% 4.11/4.36      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))
% 4.11/4.36         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.11/4.36      inference('split', [status(esa)], ['51'])).
% 4.11/4.36  thf('53', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X12 @ X10)
% 4.11/4.36          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['37'])).
% 4.11/4.36  thf('54', plain,
% 4.11/4.36      ((![X0 : $i]:
% 4.11/4.36          (~ (r2_hidden @ X0 @ sk_A)
% 4.11/4.36           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B_1))))
% 4.11/4.36         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.11/4.36      inference('sup-', [status(thm)], ['52', '53'])).
% 4.11/4.36  thf('55', plain,
% 4.11/4.36      ((~ (r2_hidden @ sk_B_1 @ sk_A))
% 4.11/4.36         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.11/4.36      inference('sup-', [status(thm)], ['50', '54'])).
% 4.11/4.36  thf('56', plain,
% 4.11/4.36      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 4.11/4.36       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['2', '55'])).
% 4.11/4.36  thf('57', plain,
% 4.11/4.36      (~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 4.11/4.36       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 4.11/4.36      inference('split', [status(esa)], ['51'])).
% 4.11/4.36  thf('58', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1) = (k1_tarski @ X0))
% 4.11/4.36          | (r2_hidden @ X0 @ X1))),
% 4.11/4.36      inference('sup+', [status(thm)], ['32', '35'])).
% 4.11/4.36  thf('59', plain,
% 4.11/4.36      (![X14 : $i]:
% 4.11/4.36         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 4.11/4.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.11/4.36  thf(commutativity_k3_xboole_0, axiom,
% 4.11/4.36    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.11/4.36  thf('60', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.11/4.36      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.11/4.36  thf(d4_xboole_0, axiom,
% 4.11/4.36    (![A:$i,B:$i,C:$i]:
% 4.11/4.36     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 4.11/4.36       ( ![D:$i]:
% 4.11/4.36         ( ( r2_hidden @ D @ C ) <=>
% 4.11/4.36           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 4.11/4.36  thf('61', plain,
% 4.11/4.36      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X6 @ X5)
% 4.11/4.36          | (r2_hidden @ X6 @ X4)
% 4.11/4.36          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 4.11/4.36      inference('cnf', [status(esa)], [d4_xboole_0])).
% 4.11/4.36  thf('62', plain,
% 4.11/4.36      (![X3 : $i, X4 : $i, X6 : $i]:
% 4.11/4.36         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['61'])).
% 4.11/4.36  thf('63', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['60', '62'])).
% 4.11/4.36  thf('64', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.11/4.36          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 4.11/4.36      inference('sup-', [status(thm)], ['59', '63'])).
% 4.11/4.36  thf('65', plain,
% 4.11/4.36      (![X14 : $i]:
% 4.11/4.36         (((X14) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X14) @ X14))),
% 4.11/4.36      inference('cnf', [status(esa)], [t7_xboole_0])).
% 4.11/4.36  thf('66', plain,
% 4.11/4.36      (![X3 : $i, X4 : $i, X6 : $i]:
% 4.11/4.36         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['61'])).
% 4.11/4.36  thf('67', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 4.11/4.36          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 4.11/4.36      inference('sup-', [status(thm)], ['65', '66'])).
% 4.11/4.36  thf('68', plain,
% 4.11/4.36      (![X9 : $i, X10 : $i, X12 : $i]:
% 4.11/4.36         (~ (r2_hidden @ X12 @ X10)
% 4.11/4.36          | ~ (r2_hidden @ X12 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.11/4.36      inference('simplify', [status(thm)], ['37'])).
% 4.11/4.36  thf('69', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.36         (((k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 4.11/4.36          | ~ (r2_hidden @ 
% 4.11/4.36               (sk_B @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))) @ X0))),
% 4.11/4.36      inference('sup-', [status(thm)], ['67', '68'])).
% 4.11/4.36  thf('70', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))
% 4.11/4.36          | ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['64', '69'])).
% 4.11/4.36  thf('71', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.11/4.36      inference('simplify', [status(thm)], ['70'])).
% 4.11/4.36  thf(t100_xboole_1, axiom,
% 4.11/4.36    (![A:$i,B:$i]:
% 4.11/4.36     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.11/4.36  thf('72', plain,
% 4.11/4.36      (![X15 : $i, X16 : $i]:
% 4.11/4.36         ((k4_xboole_0 @ X15 @ X16)
% 4.11/4.36           = (k5_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16)))),
% 4.11/4.36      inference('cnf', [status(esa)], [t100_xboole_1])).
% 4.11/4.36  thf('73', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 4.11/4.36           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 4.11/4.36      inference('sup+', [status(thm)], ['71', '72'])).
% 4.11/4.36  thf(t5_boole, axiom,
% 4.11/4.36    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.11/4.36  thf('74', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 4.11/4.36      inference('cnf', [status(esa)], [t5_boole])).
% 4.11/4.36  thf('75', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.11/4.36      inference('demod', [status(thm)], ['73', '74'])).
% 4.11/4.36  thf('76', plain,
% 4.11/4.36      (![X0 : $i, X1 : $i]:
% 4.11/4.36         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 4.11/4.36          | (r2_hidden @ X0 @ X1))),
% 4.11/4.36      inference('sup+', [status(thm)], ['58', '75'])).
% 4.11/4.36  thf('77', plain,
% 4.11/4.36      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) != (sk_A)))
% 4.11/4.36         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.11/4.36      inference('split', [status(esa)], ['0'])).
% 4.11/4.36  thf('78', plain,
% 4.11/4.36      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B_1 @ sk_A)))
% 4.11/4.36         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.11/4.36      inference('sup-', [status(thm)], ['76', '77'])).
% 4.11/4.36  thf('79', plain,
% 4.11/4.36      (((r2_hidden @ sk_B_1 @ sk_A))
% 4.11/4.36         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A))))),
% 4.11/4.36      inference('simplify', [status(thm)], ['78'])).
% 4.11/4.36  thf('80', plain,
% 4.11/4.36      ((~ (r2_hidden @ sk_B_1 @ sk_A)) <= (~ ((r2_hidden @ sk_B_1 @ sk_A)))),
% 4.11/4.36      inference('split', [status(esa)], ['51'])).
% 4.11/4.36  thf('81', plain,
% 4.11/4.36      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 4.11/4.36       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B_1)) = (sk_A)))),
% 4.11/4.36      inference('sup-', [status(thm)], ['79', '80'])).
% 4.11/4.36  thf('82', plain, ($false),
% 4.11/4.36      inference('sat_resolution*', [status(thm)], ['1', '56', '57', '81'])).
% 4.11/4.36  
% 4.11/4.36  % SZS output end Refutation
% 4.11/4.36  
% 4.11/4.37  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
