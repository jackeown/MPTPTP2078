%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JqRIITQiEd

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:01 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 168 expanded)
%              Number of leaves         :   25 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  828 (1396 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t34_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
          <=> ( r1_ordinal1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
            <=> ( r1_ordinal1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_ordinal1])).

thf('0',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X26: $i] :
      ( ( k1_ordinal1 @ X26 )
      = ( k2_xboole_0 @ X26 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf('17',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf('18',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('19',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_ordinal1 @ X29 )
      | ( r1_ordinal1 @ X30 @ X29 )
      | ( r2_hidden @ X29 @ X30 )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( sk_A = sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_ordinal1 @ X29 )
      | ( r1_ordinal1 @ X30 @ X29 )
      | ( r2_hidden @ X29 @ X30 )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ sk_A )
      | ( r1_ordinal1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_A )
    | ~ ( v3_ordinal1 @ sk_A ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    r1_ordinal1 @ sk_A @ sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,(
    ! [X26: $i] :
      ( ( k1_ordinal1 @ X26 )
      = ( k2_xboole_0 @ X26 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('42',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('43',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('44',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('48',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','53'])).

thf('55',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('56',plain,(
    ! [X26: $i] :
      ( ( k1_ordinal1 @ X26 )
      = ( k2_xboole_0 @ X26 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_ordinal1 @ X0 )
      = ( k2_xboole_0 @ X0 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v3_ordinal1 @ X29 )
      | ( r1_ordinal1 @ X30 @ X29 )
      | ( r2_hidden @ X29 @ X30 )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('59',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('60',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('64',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X28 )
      | ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_ordinal1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('69',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('74',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v3_ordinal1 @ X27 )
      | ~ ( v3_ordinal1 @ X28 )
      | ( r1_tarski @ X27 @ X28 )
      | ~ ( r1_ordinal1 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('75',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('79',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('80',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','83'])).

thf('85',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JqRIITQiEd
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:17:24 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.76/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/1.01  % Solved by: fo/fo7.sh
% 0.76/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/1.01  % done 712 iterations in 0.561s
% 0.76/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/1.01  % SZS output start Refutation
% 0.76/1.01  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.76/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/1.01  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/1.01  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.76/1.01  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.76/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/1.01  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/1.01  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.76/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.76/1.01  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.76/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.76/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/1.01  thf(t34_ordinal1, conjecture,
% 0.76/1.01    (![A:$i]:
% 0.76/1.01     ( ( v3_ordinal1 @ A ) =>
% 0.76/1.01       ( ![B:$i]:
% 0.76/1.01         ( ( v3_ordinal1 @ B ) =>
% 0.76/1.01           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.76/1.01             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.76/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.76/1.01    (~( ![A:$i]:
% 0.76/1.01        ( ( v3_ordinal1 @ A ) =>
% 0.76/1.01          ( ![B:$i]:
% 0.76/1.01            ( ( v3_ordinal1 @ B ) =>
% 0.76/1.01              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.76/1.01                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.76/1.01    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.76/1.01  thf('0', plain,
% 0.76/1.01      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.76/1.01        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('1', plain,
% 0.76/1.01      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.76/1.01       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.76/1.01      inference('split', [status(esa)], ['0'])).
% 0.76/1.01  thf(d1_enumset1, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.76/1.01       ( ![E:$i]:
% 0.76/1.01         ( ( r2_hidden @ E @ D ) <=>
% 0.76/1.01           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.76/1.01  thf(zf_stmt_1, axiom,
% 0.76/1.01    (![E:$i,C:$i,B:$i,A:$i]:
% 0.76/1.01     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.76/1.01       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.76/1.01  thf('2', plain,
% 0.76/1.01      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.76/1.01         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.76/1.01          | ((X12) = (X13))
% 0.76/1.01          | ((X12) = (X14))
% 0.76/1.01          | ((X12) = (X15)))),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/1.01  thf('3', plain,
% 0.76/1.01      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.01  thf('4', plain,
% 0.76/1.01      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.76/1.01         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.01      inference('split', [status(esa)], ['3'])).
% 0.76/1.01  thf(d1_ordinal1, axiom,
% 0.76/1.01    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.76/1.01  thf('5', plain,
% 0.76/1.01      (![X26 : $i]:
% 0.76/1.01         ((k1_ordinal1 @ X26) = (k2_xboole_0 @ X26 @ (k1_tarski @ X26)))),
% 0.76/1.01      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.76/1.01  thf(d3_xboole_0, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i]:
% 0.76/1.01     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.76/1.01       ( ![D:$i]:
% 0.76/1.01         ( ( r2_hidden @ D @ C ) <=>
% 0.76/1.01           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.76/1.01  thf('6', plain,
% 0.76/1.01      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X6 @ X4)
% 0.76/1.01          | (r2_hidden @ X6 @ X5)
% 0.76/1.01          | (r2_hidden @ X6 @ X3)
% 0.76/1.01          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.76/1.01      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.76/1.01  thf('7', plain,
% 0.76/1.01      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.76/1.01         ((r2_hidden @ X6 @ X3)
% 0.76/1.01          | (r2_hidden @ X6 @ X5)
% 0.76/1.01          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.76/1.01      inference('simplify', [status(thm)], ['6'])).
% 0.76/1.01  thf('8', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.76/1.01          | (r2_hidden @ X1 @ X0)
% 0.76/1.01          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.76/1.01      inference('sup-', [status(thm)], ['5', '7'])).
% 0.76/1.01  thf('9', plain,
% 0.76/1.01      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.76/1.01         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.01      inference('sup-', [status(thm)], ['4', '8'])).
% 0.76/1.01  thf(t69_enumset1, axiom,
% 0.76/1.01    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.76/1.01  thf('10', plain,
% 0.76/1.01      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.76/1.01      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/1.01  thf(t70_enumset1, axiom,
% 0.76/1.01    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.76/1.01  thf('11', plain,
% 0.76/1.01      (![X24 : $i, X25 : $i]:
% 0.76/1.01         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.76/1.01      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.76/1.01  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.76/1.01  thf(zf_stmt_3, axiom,
% 0.76/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/1.01     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.76/1.01       ( ![E:$i]:
% 0.76/1.01         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.76/1.01  thf('12', plain,
% 0.76/1.01      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X21 @ X20)
% 0.76/1.01          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.76/1.01          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.76/1.01      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/1.01  thf('13', plain,
% 0.76/1.01      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.76/1.01         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.76/1.01          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.76/1.01      inference('simplify', [status(thm)], ['12'])).
% 0.76/1.01  thf('14', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.76/1.01          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.76/1.01      inference('sup-', [status(thm)], ['11', '13'])).
% 0.76/1.01  thf('15', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.76/1.01          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.76/1.01      inference('sup-', [status(thm)], ['10', '14'])).
% 0.76/1.01  thf('16', plain,
% 0.76/1.01      ((((r2_hidden @ sk_A @ sk_B)
% 0.76/1.01         | ~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)))
% 0.76/1.01         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.01      inference('sup-', [status(thm)], ['9', '15'])).
% 0.76/1.01  thf('17', plain,
% 0.76/1.01      (((((sk_A) = (sk_B))
% 0.76/1.01         | ((sk_A) = (sk_B))
% 0.76/1.01         | ((sk_A) = (sk_B))
% 0.76/1.01         | (r2_hidden @ sk_A @ sk_B)))
% 0.76/1.01         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.01      inference('sup-', [status(thm)], ['2', '16'])).
% 0.76/1.01  thf('18', plain,
% 0.76/1.01      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.76/1.01         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.01      inference('simplify', [status(thm)], ['17'])).
% 0.76/1.01  thf(t26_ordinal1, axiom,
% 0.76/1.01    (![A:$i]:
% 0.76/1.01     ( ( v3_ordinal1 @ A ) =>
% 0.76/1.01       ( ![B:$i]:
% 0.76/1.01         ( ( v3_ordinal1 @ B ) =>
% 0.76/1.01           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.76/1.01  thf('19', plain,
% 0.76/1.01      (![X29 : $i, X30 : $i]:
% 0.76/1.01         (~ (v3_ordinal1 @ X29)
% 0.76/1.01          | (r1_ordinal1 @ X30 @ X29)
% 0.76/1.01          | (r2_hidden @ X29 @ X30)
% 0.76/1.01          | ~ (v3_ordinal1 @ X30))),
% 0.76/1.01      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.76/1.01  thf(antisymmetry_r2_hidden, axiom,
% 0.76/1.01    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.76/1.01  thf('20', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/1.01      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.76/1.01  thf('21', plain,
% 0.76/1.01      (![X0 : $i, X1 : $i]:
% 0.76/1.01         (~ (v3_ordinal1 @ X0)
% 0.76/1.01          | (r1_ordinal1 @ X0 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X1)
% 0.76/1.02          | ~ (r2_hidden @ X0 @ X1))),
% 0.76/1.02      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/1.02  thf('22', plain,
% 0.76/1.02      (((((sk_A) = (sk_B))
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_B)
% 0.76/1.02         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_A)))
% 0.76/1.02         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('sup-', [status(thm)], ['18', '21'])).
% 0.76/1.02  thf('23', plain, ((v3_ordinal1 @ sk_B)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('25', plain,
% 0.76/1.02      (((((sk_A) = (sk_B)) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.76/1.02         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.76/1.02  thf('26', plain,
% 0.76/1.02      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('split', [status(esa)], ['0'])).
% 0.76/1.02  thf('27', plain,
% 0.76/1.02      ((((sk_A) = (sk_B)))
% 0.76/1.02         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.76/1.02             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('sup-', [status(thm)], ['25', '26'])).
% 0.76/1.02  thf('28', plain,
% 0.76/1.02      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('split', [status(esa)], ['0'])).
% 0.76/1.02  thf('29', plain,
% 0.76/1.02      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.76/1.02         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.76/1.02             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('sup-', [status(thm)], ['27', '28'])).
% 0.76/1.02  thf('30', plain, ((v3_ordinal1 @ sk_A)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('31', plain,
% 0.76/1.02      (![X29 : $i, X30 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X29)
% 0.76/1.02          | (r1_ordinal1 @ X30 @ X29)
% 0.76/1.02          | (r2_hidden @ X29 @ X30)
% 0.76/1.02          | ~ (v3_ordinal1 @ X30))),
% 0.76/1.02      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.76/1.02  thf('32', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X0)
% 0.76/1.02          | (r1_ordinal1 @ X0 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X1)
% 0.76/1.02          | ~ (r2_hidden @ X0 @ X1))),
% 0.76/1.02      inference('sup-', [status(thm)], ['19', '20'])).
% 0.76/1.02  thf('33', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X0)
% 0.76/1.02          | (r1_ordinal1 @ X0 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X0)
% 0.76/1.02          | (r1_ordinal1 @ X1 @ X0)
% 0.76/1.02          | ~ (v3_ordinal1 @ X1))),
% 0.76/1.02      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/1.02  thf('34', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i]:
% 0.76/1.02         ((r1_ordinal1 @ X1 @ X0)
% 0.76/1.02          | ~ (v3_ordinal1 @ X1)
% 0.76/1.02          | (r1_ordinal1 @ X0 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X0))),
% 0.76/1.02      inference('simplify', [status(thm)], ['33'])).
% 0.76/1.02  thf('35', plain,
% 0.76/1.02      (![X0 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X0)
% 0.76/1.02          | (r1_ordinal1 @ X0 @ sk_A)
% 0.76/1.02          | (r1_ordinal1 @ sk_A @ X0))),
% 0.76/1.02      inference('sup-', [status(thm)], ['30', '34'])).
% 0.76/1.02  thf('36', plain, (((r1_ordinal1 @ sk_A @ sk_A) | ~ (v3_ordinal1 @ sk_A))),
% 0.76/1.02      inference('eq_fact', [status(thm)], ['35'])).
% 0.76/1.02  thf('37', plain, ((v3_ordinal1 @ sk_A)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('38', plain, ((r1_ordinal1 @ sk_A @ sk_A)),
% 0.76/1.02      inference('demod', [status(thm)], ['36', '37'])).
% 0.76/1.02  thf('39', plain,
% 0.76/1.02      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.76/1.02       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.76/1.02      inference('demod', [status(thm)], ['29', '38'])).
% 0.76/1.02  thf('40', plain,
% 0.76/1.02      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.76/1.02       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.76/1.02      inference('split', [status(esa)], ['3'])).
% 0.76/1.02  thf('41', plain,
% 0.76/1.02      (![X26 : $i]:
% 0.76/1.02         ((k1_ordinal1 @ X26) = (k2_xboole_0 @ X26 @ (k1_tarski @ X26)))),
% 0.76/1.02      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.76/1.02  thf('42', plain,
% 0.76/1.02      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.76/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/1.02  thf('43', plain,
% 0.76/1.02      (![X24 : $i, X25 : $i]:
% 0.76/1.02         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.76/1.02      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.76/1.02  thf('44', plain,
% 0.76/1.02      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.76/1.02         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.76/1.02          | (r2_hidden @ X16 @ X20)
% 0.76/1.02          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/1.02  thf('45', plain,
% 0.76/1.02      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.76/1.02         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.76/1.02          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.76/1.02      inference('simplify', [status(thm)], ['44'])).
% 0.76/1.02  thf('46', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.02         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.76/1.02          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.76/1.02      inference('sup+', [status(thm)], ['43', '45'])).
% 0.76/1.02  thf('47', plain,
% 0.76/1.02      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.76/1.02         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/1.02  thf('48', plain,
% 0.76/1.02      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.76/1.02         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.76/1.02      inference('simplify', [status(thm)], ['47'])).
% 0.76/1.02  thf('49', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.76/1.02      inference('sup-', [status(thm)], ['46', '48'])).
% 0.76/1.02  thf('50', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.76/1.02      inference('sup+', [status(thm)], ['42', '49'])).
% 0.76/1.02  thf('51', plain,
% 0.76/1.02      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.76/1.02         (~ (r2_hidden @ X2 @ X3)
% 0.76/1.02          | (r2_hidden @ X2 @ X4)
% 0.76/1.02          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.76/1.02      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.76/1.02  thf('52', plain,
% 0.76/1.02      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.76/1.02         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.76/1.02      inference('simplify', [status(thm)], ['51'])).
% 0.76/1.02  thf('53', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i]:
% 0.76/1.02         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['50', '52'])).
% 0.76/1.02  thf('54', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.76/1.02      inference('sup+', [status(thm)], ['41', '53'])).
% 0.76/1.02  thf('55', plain,
% 0.76/1.02      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.76/1.02      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/1.02  thf('56', plain,
% 0.76/1.02      (![X26 : $i]:
% 0.76/1.02         ((k1_ordinal1 @ X26) = (k2_xboole_0 @ X26 @ (k1_tarski @ X26)))),
% 0.76/1.02      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.76/1.02  thf('57', plain,
% 0.76/1.02      (![X0 : $i]:
% 0.76/1.02         ((k1_ordinal1 @ X0) = (k2_xboole_0 @ X0 @ (k2_tarski @ X0 @ X0)))),
% 0.76/1.02      inference('sup+', [status(thm)], ['55', '56'])).
% 0.76/1.02  thf('58', plain,
% 0.76/1.02      (![X29 : $i, X30 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X29)
% 0.76/1.02          | (r1_ordinal1 @ X30 @ X29)
% 0.76/1.02          | (r2_hidden @ X29 @ X30)
% 0.76/1.02          | ~ (v3_ordinal1 @ X30))),
% 0.76/1.02      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.76/1.02  thf('59', plain,
% 0.76/1.02      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.76/1.02         (~ (r2_hidden @ X2 @ X5)
% 0.76/1.02          | (r2_hidden @ X2 @ X4)
% 0.76/1.02          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.76/1.02      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.76/1.02  thf('60', plain,
% 0.76/1.02      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.76/1.02         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.76/1.02      inference('simplify', [status(thm)], ['59'])).
% 0.76/1.02  thf('61', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X0)
% 0.76/1.02          | (r1_ordinal1 @ X0 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X1)
% 0.76/1.02          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['58', '60'])).
% 0.76/1.02  thf('62', plain,
% 0.76/1.02      (![X0 : $i, X1 : $i]:
% 0.76/1.02         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.76/1.02          | ~ (v3_ordinal1 @ X1)
% 0.76/1.02          | (r1_ordinal1 @ X0 @ X1)
% 0.76/1.02          | ~ (v3_ordinal1 @ X0))),
% 0.76/1.02      inference('sup+', [status(thm)], ['57', '61'])).
% 0.76/1.02  thf('63', plain,
% 0.76/1.02      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('split', [status(esa)], ['0'])).
% 0.76/1.02  thf('64', plain,
% 0.76/1.02      (((~ (v3_ordinal1 @ sk_B)
% 0.76/1.02         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_A)))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('sup-', [status(thm)], ['62', '63'])).
% 0.76/1.02  thf('65', plain, ((v3_ordinal1 @ sk_B)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('66', plain, ((v3_ordinal1 @ sk_A)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('67', plain,
% 0.76/1.02      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.76/1.02  thf(redefinition_r1_ordinal1, axiom,
% 0.76/1.02    (![A:$i,B:$i]:
% 0.76/1.02     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.76/1.02       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.76/1.02  thf('68', plain,
% 0.76/1.02      (![X27 : $i, X28 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X27)
% 0.76/1.02          | ~ (v3_ordinal1 @ X28)
% 0.76/1.02          | (r1_tarski @ X27 @ X28)
% 0.76/1.02          | ~ (r1_ordinal1 @ X27 @ X28))),
% 0.76/1.02      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.76/1.02  thf('69', plain,
% 0.76/1.02      ((((r1_tarski @ sk_B @ sk_A)
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_A)
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_B)))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('sup-', [status(thm)], ['67', '68'])).
% 0.76/1.02  thf('70', plain, ((v3_ordinal1 @ sk_A)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('71', plain, ((v3_ordinal1 @ sk_B)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('72', plain,
% 0.76/1.02      (((r1_tarski @ sk_B @ sk_A))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.76/1.02  thf('73', plain,
% 0.76/1.02      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('split', [status(esa)], ['3'])).
% 0.76/1.02  thf('74', plain,
% 0.76/1.02      (![X27 : $i, X28 : $i]:
% 0.76/1.02         (~ (v3_ordinal1 @ X27)
% 0.76/1.02          | ~ (v3_ordinal1 @ X28)
% 0.76/1.02          | (r1_tarski @ X27 @ X28)
% 0.76/1.02          | ~ (r1_ordinal1 @ X27 @ X28))),
% 0.76/1.02      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.76/1.02  thf('75', plain,
% 0.76/1.02      ((((r1_tarski @ sk_A @ sk_B)
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_B)
% 0.76/1.02         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/1.02  thf('76', plain, ((v3_ordinal1 @ sk_B)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('77', plain, ((v3_ordinal1 @ sk_A)),
% 0.76/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/1.02  thf('78', plain,
% 0.76/1.02      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.76/1.02  thf(d10_xboole_0, axiom,
% 0.76/1.02    (![A:$i,B:$i]:
% 0.76/1.02     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/1.02  thf('79', plain,
% 0.76/1.02      (![X8 : $i, X10 : $i]:
% 0.76/1.02         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.76/1.02      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/1.02  thf('80', plain,
% 0.76/1.02      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A))))
% 0.76/1.02         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['78', '79'])).
% 0.76/1.02  thf('81', plain,
% 0.76/1.02      ((((sk_B) = (sk_A)))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.76/1.02             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['72', '80'])).
% 0.76/1.02  thf('82', plain,
% 0.76/1.02      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.76/1.02      inference('split', [status(esa)], ['0'])).
% 0.76/1.02  thf('83', plain,
% 0.76/1.02      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.76/1.02         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.76/1.02             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['81', '82'])).
% 0.76/1.02  thf('84', plain,
% 0.76/1.02      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.76/1.02       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.76/1.02      inference('sup-', [status(thm)], ['54', '83'])).
% 0.76/1.02  thf('85', plain, ($false),
% 0.76/1.02      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '84'])).
% 0.76/1.02  
% 0.76/1.02  % SZS output end Refutation
% 0.76/1.02  
% 0.76/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
