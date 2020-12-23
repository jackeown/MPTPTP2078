%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nOR7VpORlr

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:41 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 125 expanded)
%              Number of leaves         :   31 (  48 expanded)
%              Depth                    :   12
%              Number of atoms          :  702 (1010 expanded)
%              Number of equality atoms :   64 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('0',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k11_relat_1 @ X20 @ X21 )
        = ( k9_relat_1 @ X20 @ ( k1_tarski @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k9_relat_1 @ X29 @ X30 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k9_relat_1 @ X29 @ X30 )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('24',plain,(
    ! [X17: $i] :
      ( ( k2_tarski @ X17 @ X17 )
      = ( k1_tarski @ X17 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k1_enumset1 @ X18 @ X18 @ X19 )
      = ( k2_tarski @ X18 @ X19 ) ) ),
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

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X5 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('30',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X5 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('39',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k11_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('41',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X24 )
      | ( r2_hidden @ X22 @ X25 )
      | ( X25
       != ( k1_relat_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('42',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X22 @ X23 ) @ X24 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k11_relat_1 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('44',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('45',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('46',plain,(
    ! [X4: $i] :
      ( ( X4 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( ( X4 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('54',plain,
    ( ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('58',plain,
    ( ( o_0_0_xboole_0 != k1_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('60',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','36','37','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.16/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.16/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nOR7VpORlr
% 0.17/0.37  % Computer   : n010.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 11:57:00 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.51/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.68  % Solved by: fo/fo7.sh
% 0.51/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.68  % done 286 iterations in 0.198s
% 0.51/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.68  % SZS output start Refutation
% 0.51/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.51/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.51/0.68  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.51/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.51/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.68  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.51/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.51/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.68  thf(t205_relat_1, conjecture,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( v1_relat_1 @ B ) =>
% 0.51/0.68       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.51/0.68         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.51/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.68    (~( ![A:$i,B:$i]:
% 0.51/0.68        ( ( v1_relat_1 @ B ) =>
% 0.51/0.68          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.51/0.68            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.51/0.68    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.51/0.68  thf('0', plain,
% 0.51/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.51/0.68        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('1', plain,
% 0.51/0.68      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.51/0.68       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.51/0.68      inference('split', [status(esa)], ['0'])).
% 0.51/0.68  thf('2', plain,
% 0.51/0.68      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.51/0.68         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.51/0.68      inference('split', [status(esa)], ['0'])).
% 0.51/0.68  thf('3', plain,
% 0.51/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.51/0.68        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('4', plain,
% 0.51/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('split', [status(esa)], ['3'])).
% 0.51/0.68  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.51/0.68  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.51/0.68      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.51/0.68  thf('6', plain,
% 0.51/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (o_0_0_xboole_0)))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.51/0.68  thf(d16_relat_1, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ( v1_relat_1 @ A ) =>
% 0.51/0.68       ( ![B:$i]:
% 0.51/0.68         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.51/0.68  thf('7', plain,
% 0.51/0.68      (![X20 : $i, X21 : $i]:
% 0.51/0.68         (((k11_relat_1 @ X20 @ X21) = (k9_relat_1 @ X20 @ (k1_tarski @ X21)))
% 0.51/0.68          | ~ (v1_relat_1 @ X20))),
% 0.51/0.68      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.51/0.68  thf(t151_relat_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( v1_relat_1 @ B ) =>
% 0.51/0.68       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.51/0.68         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.51/0.68  thf('8', plain,
% 0.51/0.68      (![X29 : $i, X30 : $i]:
% 0.51/0.68         (((k9_relat_1 @ X29 @ X30) != (k1_xboole_0))
% 0.51/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X29) @ X30)
% 0.51/0.68          | ~ (v1_relat_1 @ X29))),
% 0.51/0.68      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.51/0.68  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.51/0.68      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.51/0.68  thf('10', plain,
% 0.51/0.68      (![X29 : $i, X30 : $i]:
% 0.51/0.68         (((k9_relat_1 @ X29 @ X30) != (o_0_0_xboole_0))
% 0.51/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X29) @ X30)
% 0.51/0.68          | ~ (v1_relat_1 @ X29))),
% 0.51/0.68      inference('demod', [status(thm)], ['8', '9'])).
% 0.51/0.68  thf('11', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (((k11_relat_1 @ X1 @ X0) != (o_0_0_xboole_0))
% 0.51/0.68          | ~ (v1_relat_1 @ X1)
% 0.51/0.68          | ~ (v1_relat_1 @ X1)
% 0.51/0.68          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['7', '10'])).
% 0.51/0.68  thf('12', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.51/0.68          | ~ (v1_relat_1 @ X1)
% 0.51/0.68          | ((k11_relat_1 @ X1 @ X0) != (o_0_0_xboole_0)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['11'])).
% 0.51/0.68  thf('13', plain,
% 0.51/0.68      (((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.51/0.68         | ~ (v1_relat_1 @ sk_B_1)
% 0.51/0.68         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['6', '12'])).
% 0.51/0.68  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('15', plain,
% 0.51/0.68      (((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.51/0.68         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A))))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('demod', [status(thm)], ['13', '14'])).
% 0.51/0.68  thf('16', plain,
% 0.51/0.68      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ (k1_tarski @ sk_A)))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('simplify', [status(thm)], ['15'])).
% 0.51/0.68  thf(t3_xboole_0, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.51/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.68            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.51/0.68  thf('17', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.68  thf('18', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.68  thf('19', plain,
% 0.51/0.68      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X2 @ X0)
% 0.51/0.68          | ~ (r2_hidden @ X2 @ X3)
% 0.51/0.68          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.68  thf('20', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ X1 @ X0)
% 0.51/0.68          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.51/0.68          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.51/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.51/0.68  thf('21', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ X0 @ X1)
% 0.51/0.68          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.51/0.68          | (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['17', '20'])).
% 0.51/0.68  thf('22', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.68      inference('simplify', [status(thm)], ['21'])).
% 0.51/0.68  thf('23', plain,
% 0.51/0.68      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B_1)))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['16', '22'])).
% 0.51/0.68  thf(t69_enumset1, axiom,
% 0.51/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.68  thf('24', plain,
% 0.51/0.68      (![X17 : $i]: ((k2_tarski @ X17 @ X17) = (k1_tarski @ X17))),
% 0.51/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.68  thf(t70_enumset1, axiom,
% 0.51/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.51/0.68  thf('25', plain,
% 0.51/0.68      (![X18 : $i, X19 : $i]:
% 0.51/0.68         ((k1_enumset1 @ X18 @ X18 @ X19) = (k2_tarski @ X18 @ X19))),
% 0.51/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.51/0.68  thf(d1_enumset1, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.51/0.68       ( ![E:$i]:
% 0.51/0.68         ( ( r2_hidden @ E @ D ) <=>
% 0.51/0.68           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.51/0.68  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.51/0.68  thf(zf_stmt_2, axiom,
% 0.51/0.68    (![E:$i,C:$i,B:$i,A:$i]:
% 0.51/0.68     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.51/0.68       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.51/0.68  thf(zf_stmt_3, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.51/0.68       ( ![E:$i]:
% 0.51/0.68         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.51/0.68  thf('26', plain,
% 0.51/0.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.51/0.68         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.51/0.68          | (r2_hidden @ X10 @ X14)
% 0.51/0.68          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.51/0.68  thf('27', plain,
% 0.51/0.68      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.51/0.68         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.51/0.68          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.51/0.68      inference('simplify', [status(thm)], ['26'])).
% 0.51/0.68  thf('28', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.51/0.68          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.51/0.68      inference('sup+', [status(thm)], ['25', '27'])).
% 0.51/0.68  thf('29', plain,
% 0.51/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.51/0.68         (((X6) != (X5)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.51/0.68  thf('30', plain,
% 0.51/0.68      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X5 @ X7 @ X8 @ X5)),
% 0.51/0.68      inference('simplify', [status(thm)], ['29'])).
% 0.51/0.68  thf('31', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['28', '30'])).
% 0.51/0.68  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.51/0.68      inference('sup+', [status(thm)], ['24', '31'])).
% 0.51/0.68  thf('33', plain,
% 0.51/0.68      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X2 @ X0)
% 0.51/0.68          | ~ (r2_hidden @ X2 @ X3)
% 0.51/0.68          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.68  thf('34', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.68  thf('35', plain,
% 0.51/0.68      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.51/0.68         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['23', '34'])).
% 0.51/0.68  thf('36', plain,
% 0.51/0.68      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.51/0.68       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['2', '35'])).
% 0.51/0.68  thf('37', plain,
% 0.51/0.68      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.51/0.68       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.51/0.68      inference('split', [status(esa)], ['3'])).
% 0.51/0.68  thf('38', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.68  thf(t204_relat_1, axiom,
% 0.51/0.68    (![A:$i,B:$i,C:$i]:
% 0.51/0.68     ( ( v1_relat_1 @ C ) =>
% 0.51/0.68       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.51/0.68         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.51/0.68  thf('39', plain,
% 0.51/0.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.51/0.68          | (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.51/0.68          | ~ (v1_relat_1 @ X32))),
% 0.51/0.68      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.51/0.68  thf('40', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         ((r1_xboole_0 @ (k11_relat_1 @ X1 @ X0) @ X2)
% 0.51/0.68          | ~ (v1_relat_1 @ X1)
% 0.51/0.68          | (r2_hidden @ 
% 0.51/0.68             (k4_tarski @ X0 @ (sk_C @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.68  thf(d4_relat_1, axiom,
% 0.51/0.68    (![A:$i,B:$i]:
% 0.51/0.68     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.51/0.68       ( ![C:$i]:
% 0.51/0.68         ( ( r2_hidden @ C @ B ) <=>
% 0.51/0.68           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.51/0.68  thf('41', plain,
% 0.51/0.68      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.51/0.68         (~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ X24)
% 0.51/0.68          | (r2_hidden @ X22 @ X25)
% 0.51/0.68          | ((X25) != (k1_relat_1 @ X24)))),
% 0.51/0.68      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.51/0.68  thf('42', plain,
% 0.51/0.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.51/0.68         ((r2_hidden @ X22 @ (k1_relat_1 @ X24))
% 0.51/0.68          | ~ (r2_hidden @ (k4_tarski @ X22 @ X23) @ X24))),
% 0.51/0.68      inference('simplify', [status(thm)], ['41'])).
% 0.51/0.68  thf('43', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.68         (~ (v1_relat_1 @ X0)
% 0.51/0.68          | (r1_xboole_0 @ (k11_relat_1 @ X0 @ X1) @ X2)
% 0.51/0.68          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['40', '42'])).
% 0.51/0.68  thf(t7_xboole_0, axiom,
% 0.51/0.68    (![A:$i]:
% 0.51/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.51/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.51/0.68  thf('44', plain,
% 0.51/0.68      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.51/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.51/0.68  thf('45', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.51/0.68      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.51/0.68  thf('46', plain,
% 0.51/0.68      (![X4 : $i]: (((X4) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.51/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.68  thf('47', plain,
% 0.51/0.68      (![X4 : $i]: (((X4) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.51/0.68      inference('demod', [status(thm)], ['44', '45'])).
% 0.51/0.68  thf('48', plain,
% 0.51/0.68      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.51/0.68         (~ (r2_hidden @ X2 @ X0)
% 0.51/0.68          | ~ (r2_hidden @ X2 @ X3)
% 0.51/0.68          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.51/0.68      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.51/0.68  thf('49', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         (((X0) = (o_0_0_xboole_0))
% 0.51/0.68          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.51/0.68          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.51/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.51/0.68  thf('50', plain,
% 0.51/0.68      (![X0 : $i]:
% 0.51/0.68         (((X0) = (o_0_0_xboole_0))
% 0.51/0.68          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.51/0.68          | ((X0) = (o_0_0_xboole_0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['46', '49'])).
% 0.51/0.68  thf('51', plain,
% 0.51/0.68      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (o_0_0_xboole_0)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['50'])).
% 0.51/0.68  thf('52', plain,
% 0.51/0.68      (![X0 : $i, X1 : $i]:
% 0.51/0.68         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.51/0.68          | ~ (v1_relat_1 @ X1)
% 0.51/0.68          | ((k11_relat_1 @ X1 @ X0) = (o_0_0_xboole_0)))),
% 0.51/0.68      inference('sup-', [status(thm)], ['43', '51'])).
% 0.51/0.68  thf('53', plain,
% 0.51/0.68      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.51/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.51/0.68      inference('split', [status(esa)], ['3'])).
% 0.51/0.68  thf('54', plain,
% 0.51/0.68      (((((k11_relat_1 @ sk_B_1 @ sk_A) = (o_0_0_xboole_0))
% 0.51/0.68         | ~ (v1_relat_1 @ sk_B_1)))
% 0.51/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['52', '53'])).
% 0.51/0.68  thf('55', plain, ((v1_relat_1 @ sk_B_1)),
% 0.51/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.68  thf('56', plain,
% 0.51/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (o_0_0_xboole_0)))
% 0.51/0.68         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.51/0.68      inference('demod', [status(thm)], ['54', '55'])).
% 0.51/0.68  thf('57', plain,
% 0.51/0.68      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.51/0.68         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.51/0.68      inference('split', [status(esa)], ['0'])).
% 0.51/0.68  thf('58', plain,
% 0.51/0.68      ((((o_0_0_xboole_0) != (k1_xboole_0)))
% 0.51/0.68         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.51/0.68             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.51/0.68      inference('sup-', [status(thm)], ['56', '57'])).
% 0.51/0.68  thf('59', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.51/0.68      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.51/0.68  thf('60', plain,
% 0.51/0.68      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.51/0.68         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.51/0.68             ~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.51/0.68      inference('demod', [status(thm)], ['58', '59'])).
% 0.51/0.68  thf('61', plain,
% 0.51/0.68      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.51/0.68       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.51/0.68      inference('simplify', [status(thm)], ['60'])).
% 0.51/0.68  thf('62', plain, ($false),
% 0.51/0.68      inference('sat_resolution*', [status(thm)], ['1', '36', '37', '61'])).
% 0.51/0.68  
% 0.51/0.68  % SZS output end Refutation
% 0.51/0.68  
% 0.51/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
