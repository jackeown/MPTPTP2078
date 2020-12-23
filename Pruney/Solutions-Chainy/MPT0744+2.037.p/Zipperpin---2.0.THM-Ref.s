%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QHVDQDpV25

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 140 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  691 (1099 expanded)
%              Number of equality atoms :   40 (  41 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

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
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ~ ( v3_ordinal1 @ X36 )
      | ( r1_ordinal1 @ X35 @ X36 )
      | ~ ( r1_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

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

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( X13 = X14 )
      | ( X13 = X15 )
      | ( X13 = X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X31: $i] :
      ( ( k1_ordinal1 @ X31 )
      = ( k2_xboole_0 @ X31 @ ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k1_enumset1 @ X25 @ X25 @ X26 )
      = ( k2_tarski @ X25 @ X26 ) ) ),
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

thf('17',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X18 @ X19 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( v1_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('25',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('27',plain,(
    ! [X30: $i] :
      ( ( v1_ordinal1 @ X30 )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('28',plain,(
    v1_ordinal1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_tarski @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ~ ( v3_ordinal1 @ X36 )
      | ( r1_ordinal1 @ X35 @ X36 )
      | ~ ( r1_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('31',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('43',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('44',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( v3_ordinal1 @ X35 )
      | ~ ( v3_ordinal1 @ X36 )
      | ( r1_tarski @ X35 @ X36 )
      | ~ ( r1_ordinal1 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('45',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('49',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r2_xboole_0 @ X6 @ X8 )
      | ( X6 = X8 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('50',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_xboole_0 @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X40: $i,X41: $i] :
      ( ~ ( v3_ordinal1 @ X40 )
      | ( r2_hidden @ X41 @ X40 )
      | ~ ( r2_xboole_0 @ X41 @ X40 )
      | ~ ( v1_ordinal1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('52',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( v1_ordinal1 @ sk_A )
      | ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X30: $i] :
      ( ( v1_ordinal1 @ X30 )
      | ~ ( v3_ordinal1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('55',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['52','55','56'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('58',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ ( k1_ordinal1 @ X39 ) )
      | ~ ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('59',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('63',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r2_hidden @ X38 @ ( k1_ordinal1 @ X39 ) )
      | ( X38 != X39 ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('65',plain,(
    ! [X39: $i] :
      ( r2_hidden @ X39 @ ( k1_ordinal1 @ X39 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','41','42','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QHVDQDpV25
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:25:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 308 iterations in 0.137s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.37/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.60  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.37/0.60  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.37/0.60  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.37/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.37/0.60  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.37/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.37/0.60  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.37/0.60  thf(t34_ordinal1, conjecture,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v3_ordinal1 @ A ) =>
% 0.37/0.60       ( ![B:$i]:
% 0.37/0.60         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.60           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.60             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i]:
% 0.37/0.60        ( ( v3_ordinal1 @ A ) =>
% 0.37/0.60          ( ![B:$i]:
% 0.37/0.60            ( ( v3_ordinal1 @ B ) =>
% 0.37/0.60              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.60                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.37/0.60  thf('0', plain,
% 0.37/0.60      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.37/0.60        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.37/0.60       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf(d10_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.60  thf('2', plain,
% 0.37/0.60      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.60  thf('3', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.37/0.60      inference('simplify', [status(thm)], ['2'])).
% 0.37/0.60  thf(redefinition_r1_ordinal1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.37/0.60       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (![X35 : $i, X36 : $i]:
% 0.37/0.60         (~ (v3_ordinal1 @ X35)
% 0.37/0.60          | ~ (v3_ordinal1 @ X36)
% 0.37/0.60          | (r1_ordinal1 @ X35 @ X36)
% 0.37/0.60          | ~ (r1_tarski @ X35 @ X36))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.60  thf('5', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.60  thf('6', plain,
% 0.37/0.60      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.37/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.37/0.60  thf(d1_enumset1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.60       ( ![E:$i]:
% 0.37/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.37/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_1, axiom,
% 0.37/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.37/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.37/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.60         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.37/0.60          | ((X13) = (X14))
% 0.37/0.60          | ((X13) = (X15))
% 0.37/0.60          | ((X13) = (X16)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.37/0.60        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('split', [status(esa)], ['8'])).
% 0.37/0.60  thf(d1_ordinal1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X31 : $i]:
% 0.37/0.60         ((k1_ordinal1 @ X31) = (k2_xboole_0 @ X31 @ (k1_tarski @ X31)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.37/0.60  thf(d3_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.37/0.60       ( ![D:$i]:
% 0.37/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.60           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.37/0.60  thf('11', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.60          | (r2_hidden @ X4 @ X3)
% 0.37/0.60          | (r2_hidden @ X4 @ X1)
% 0.37/0.60          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.37/0.60         ((r2_hidden @ X4 @ X1)
% 0.37/0.60          | (r2_hidden @ X4 @ X3)
% 0.37/0.60          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.37/0.60          | (r2_hidden @ X1 @ X0)
% 0.37/0.60          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['10', '12'])).
% 0.37/0.60  thf('14', plain,
% 0.37/0.60      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.37/0.60         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['9', '13'])).
% 0.37/0.60  thf(t69_enumset1, axiom,
% 0.37/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.37/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.60  thf(t70_enumset1, axiom,
% 0.37/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.37/0.60  thf('16', plain,
% 0.37/0.60      (![X25 : $i, X26 : $i]:
% 0.37/0.60         ((k1_enumset1 @ X25 @ X25 @ X26) = (k2_tarski @ X25 @ X26))),
% 0.37/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.37/0.60  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.37/0.60  thf(zf_stmt_3, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.37/0.60       ( ![E:$i]:
% 0.37/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X22 @ X21)
% 0.37/0.60          | ~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.37/0.60          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (![X18 : $i, X19 : $i, X20 : $i, X22 : $i]:
% 0.37/0.60         (~ (zip_tseitin_0 @ X22 @ X18 @ X19 @ X20)
% 0.37/0.60          | ~ (r2_hidden @ X22 @ (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.37/0.60          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.37/0.60      inference('sup-', [status(thm)], ['16', '18'])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.37/0.60          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['15', '19'])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      ((((r2_hidden @ sk_A @ sk_B_1)
% 0.37/0.60         | ~ (zip_tseitin_0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['14', '20'])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1))
% 0.37/0.60         | ((sk_A) = (sk_B_1))
% 0.37/0.60         | ((sk_A) = (sk_B_1))
% 0.37/0.60         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['7', '21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('simplify', [status(thm)], ['22'])).
% 0.37/0.60  thf(d2_ordinal1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v1_ordinal1 @ A ) <=>
% 0.37/0.60       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.37/0.60  thf('24', plain,
% 0.37/0.60      (![X32 : $i, X33 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X32 @ X33)
% 0.37/0.60          | (r1_tarski @ X32 @ X33)
% 0.37/0.60          | ~ (v1_ordinal1 @ X33))),
% 0.37/0.60      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1))
% 0.37/0.60         | ~ (v1_ordinal1 @ sk_B_1)
% 0.37/0.60         | (r1_tarski @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['23', '24'])).
% 0.37/0.60  thf('26', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(cc1_ordinal1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X30 : $i]: ((v1_ordinal1 @ X30) | ~ (v3_ordinal1 @ X30))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.37/0.60  thf('28', plain, ((v1_ordinal1 @ sk_B_1)),
% 0.37/0.60      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1)) | (r1_tarski @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('demod', [status(thm)], ['25', '28'])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X35 : $i, X36 : $i]:
% 0.37/0.60         (~ (v3_ordinal1 @ X35)
% 0.37/0.60          | ~ (v3_ordinal1 @ X36)
% 0.37/0.60          | (r1_ordinal1 @ X35 @ X36)
% 0.37/0.60          | ~ (r1_tarski @ X35 @ X36))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1))
% 0.37/0.60         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.37/0.60         | ~ (v3_ordinal1 @ sk_B_1)
% 0.37/0.60         | ~ (v3_ordinal1 @ sk_A)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.60  thf('32', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('33', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('34', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1)) | (r1_ordinal1 @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      ((((sk_A) = (sk_B_1)))
% 0.37/0.60         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.37/0.60             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.37/0.60         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.37/0.60             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      ((~ (v3_ordinal1 @ sk_A))
% 0.37/0.60         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.37/0.60             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '38'])).
% 0.37/0.60  thf('40', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.37/0.60       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['39', '40'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.37/0.60       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['8'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('split', [status(esa)], ['8'])).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      (![X35 : $i, X36 : $i]:
% 0.37/0.60         (~ (v3_ordinal1 @ X35)
% 0.37/0.60          | ~ (v3_ordinal1 @ X36)
% 0.37/0.60          | (r1_tarski @ X35 @ X36)
% 0.37/0.60          | ~ (r1_ordinal1 @ X35 @ X36))),
% 0.37/0.60      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.37/0.60         | ~ (v3_ordinal1 @ sk_B_1)
% 0.37/0.60         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.37/0.60  thf('46', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('47', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('48', plain,
% 0.37/0.60      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.37/0.60  thf(d8_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.37/0.60       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.37/0.60  thf('49', plain,
% 0.37/0.60      (![X6 : $i, X8 : $i]:
% 0.37/0.60         ((r2_xboole_0 @ X6 @ X8) | ((X6) = (X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.37/0.60      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.37/0.60  thf('50', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1)) | (r2_xboole_0 @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.60  thf(t21_ordinal1, axiom,
% 0.37/0.60    (![A:$i]:
% 0.37/0.60     ( ( v1_ordinal1 @ A ) =>
% 0.37/0.60       ( ![B:$i]:
% 0.37/0.60         ( ( v3_ordinal1 @ B ) =>
% 0.37/0.60           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.37/0.60  thf('51', plain,
% 0.37/0.60      (![X40 : $i, X41 : $i]:
% 0.37/0.60         (~ (v3_ordinal1 @ X40)
% 0.37/0.60          | (r2_hidden @ X41 @ X40)
% 0.37/0.60          | ~ (r2_xboole_0 @ X41 @ X40)
% 0.37/0.60          | ~ (v1_ordinal1 @ X41))),
% 0.37/0.60      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.37/0.60  thf('52', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1))
% 0.37/0.60         | ~ (v1_ordinal1 @ sk_A)
% 0.37/0.60         | (r2_hidden @ sk_A @ sk_B_1)
% 0.37/0.60         | ~ (v3_ordinal1 @ sk_B_1))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.60  thf('53', plain, ((v3_ordinal1 @ sk_A)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('54', plain,
% 0.37/0.60      (![X30 : $i]: ((v1_ordinal1 @ X30) | ~ (v3_ordinal1 @ X30))),
% 0.37/0.60      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.37/0.60  thf('55', plain, ((v1_ordinal1 @ sk_A)),
% 0.37/0.60      inference('sup-', [status(thm)], ['53', '54'])).
% 0.37/0.60  thf('56', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('57', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ sk_B_1)))
% 0.37/0.60         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['52', '55', '56'])).
% 0.37/0.60  thf(t13_ordinal1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.37/0.60       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.37/0.60  thf('58', plain,
% 0.37/0.60      (![X38 : $i, X39 : $i]:
% 0.37/0.60         ((r2_hidden @ X38 @ (k1_ordinal1 @ X39)) | ~ (r2_hidden @ X38 @ X39))),
% 0.37/0.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.60  thf('59', plain,
% 0.37/0.60      (((((sk_A) = (sk_B_1)) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))
% 0.37/0.60         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['57', '58'])).
% 0.37/0.60  thf('60', plain,
% 0.37/0.60      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('61', plain,
% 0.37/0.60      ((((sk_A) = (sk_B_1)))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.37/0.60             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['59', '60'])).
% 0.37/0.60  thf('62', plain,
% 0.37/0.60      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.37/0.60      inference('split', [status(esa)], ['0'])).
% 0.37/0.60  thf('63', plain,
% 0.37/0.60      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.37/0.60         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.37/0.60             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.60  thf('64', plain,
% 0.37/0.60      (![X38 : $i, X39 : $i]:
% 0.37/0.60         ((r2_hidden @ X38 @ (k1_ordinal1 @ X39)) | ((X38) != (X39)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.37/0.60  thf('65', plain, (![X39 : $i]: (r2_hidden @ X39 @ (k1_ordinal1 @ X39))),
% 0.37/0.60      inference('simplify', [status(thm)], ['64'])).
% 0.37/0.60  thf('66', plain,
% 0.37/0.60      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.37/0.60       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.37/0.60      inference('demod', [status(thm)], ['63', '65'])).
% 0.37/0.60  thf('67', plain, ($false),
% 0.37/0.60      inference('sat_resolution*', [status(thm)], ['1', '41', '42', '66'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
