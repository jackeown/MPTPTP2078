%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7eAMt6SNdC

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:04 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 195 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  971 (1590 expanded)
%              Number of equality atoms :   52 (  73 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( v3_ordinal1 @ X78 )
      | ~ ( v3_ordinal1 @ X79 )
      | ( r1_ordinal1 @ X78 @ X79 )
      | ~ ( r1_tarski @ X78 @ X79 ) ) ),
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

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X80: $i,X81: $i] :
      ( ~ ( v3_ordinal1 @ X80 )
      | ( r1_ordinal1 @ X81 @ X80 )
      | ( r2_hidden @ X80 @ X81 )
      | ~ ( v3_ordinal1 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_hidden @ X75 @ X76 )
      | ( r1_tarski @ X75 @ X76 )
      | ~ ( v1_ordinal1 @ X76 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( X10 = X11 )
      | ( X10 = X12 )
      | ( X10 = X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['11'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('13',plain,(
    ! [X74: $i] :
      ( ( k1_ordinal1 @ X74 )
      = ( k2_xboole_0 @ X74 @ ( k1_tarski @ X74 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('15',plain,(
    ! [X74: $i] :
      ( ( k1_ordinal1 @ X74 )
      = ( k3_tarski @ ( k2_tarski @ X74 @ ( k1_tarski @ X74 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B_1 ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('22',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
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

thf('24',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,(
    ! [X15: $i,X16: $i,X17: $i,X19: $i] :
      ( ~ ( zip_tseitin_0 @ X19 @ X15 @ X16 @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,
    ( ( ( sk_A = sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( sk_A = sk_B_1 )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['10','28'])).

thf('30',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X82: $i,X83: $i] :
      ( ~ ( r2_hidden @ X82 @ X83 )
      | ~ ( r1_tarski @ X83 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('32',plain,
    ( ( ( sk_A = sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ~ ( v1_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','32'])).

thf('34',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('35',plain,(
    ! [X73: $i] :
      ( ( v1_ordinal1 @ X73 )
      | ~ ( v3_ordinal1 @ X73 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('36',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
      | ( sk_A = sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['33','36','37','38'])).

thf('40',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('41',plain,
    ( ( sk_A = sk_B_1 )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['11'])).

thf('48',plain,(
    ! [X74: $i] :
      ( ( k1_ordinal1 @ X74 )
      = ( k3_tarski @ ( k2_tarski @ X74 @ ( k1_tarski @ X74 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('50',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k2_enumset1 @ X24 @ X24 @ X25 @ X26 )
      = ( k1_enumset1 @ X24 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('55',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('60',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','66'])).

thf('68',plain,(
    ! [X74: $i] :
      ( ( k1_ordinal1 @ X74 )
      = ( k3_tarski @ ( k2_tarski @ X74 @ ( k1_tarski @ X74 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,(
    ! [X80: $i,X81: $i] :
      ( ~ ( v3_ordinal1 @ X80 )
      | ( r1_ordinal1 @ X81 @ X80 )
      | ( r2_hidden @ X80 @ X81 )
      | ~ ( v3_ordinal1 @ X81 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X49: $i,X50: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X49 @ X50 ) )
      = ( k2_xboole_0 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k3_tarski @ ( k2_tarski @ X0 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','74'])).

thf('76',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('77',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B_1 )
      | ( r1_ordinal1 @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( r1_ordinal1 @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( v3_ordinal1 @ X78 )
      | ~ ( v3_ordinal1 @ X79 )
      | ( r1_tarski @ X78 @ X79 )
      | ~ ( r1_ordinal1 @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('82',plain,
    ( ( ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('87',plain,(
    ! [X78: $i,X79: $i] :
      ( ~ ( v3_ordinal1 @ X78 )
      | ~ ( v3_ordinal1 @ X79 )
      | ( r1_tarski @ X78 @ X79 )
      | ~ ( r1_ordinal1 @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('88',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_B_1 )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r1_tarski @ sk_A @ sk_B_1 )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('93',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ( sk_B_1 = sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_B_1 = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','93'])).

thf('95',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) )
      & ( r1_ordinal1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B_1 )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['67','96'])).

thf('98',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','46','47','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7eAMt6SNdC
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.92  % Solved by: fo/fo7.sh
% 0.72/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.92  % done 1026 iterations in 0.462s
% 0.72/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.92  % SZS output start Refutation
% 0.72/0.92  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.92  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.72/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.72/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.92  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.72/0.92  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.72/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.92  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.72/0.92  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.72/0.92  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.72/0.92  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.72/0.92  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.92  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.72/0.92  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.72/0.92  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.72/0.92  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.72/0.92  thf(t34_ordinal1, conjecture,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( v3_ordinal1 @ A ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( v3_ordinal1 @ B ) =>
% 0.72/0.92           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.72/0.92             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.72/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.92    (~( ![A:$i]:
% 0.72/0.92        ( ( v3_ordinal1 @ A ) =>
% 0.72/0.92          ( ![B:$i]:
% 0.72/0.92            ( ( v3_ordinal1 @ B ) =>
% 0.72/0.92              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.72/0.92                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.72/0.92    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.72/0.92  thf('0', plain,
% 0.72/0.92      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.72/0.92        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('1', plain,
% 0.72/0.92      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.72/0.92       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf(d10_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.92  thf('2', plain,
% 0.72/0.92      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.92  thf('3', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.72/0.92      inference('simplify', [status(thm)], ['2'])).
% 0.72/0.92  thf(redefinition_r1_ordinal1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.72/0.92       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.72/0.92  thf('4', plain,
% 0.72/0.92      (![X78 : $i, X79 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X78)
% 0.72/0.92          | ~ (v3_ordinal1 @ X79)
% 0.72/0.92          | (r1_ordinal1 @ X78 @ X79)
% 0.72/0.92          | ~ (r1_tarski @ X78 @ X79))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.72/0.92  thf('5', plain,
% 0.72/0.92      (![X0 : $i]:
% 0.72/0.92         ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['3', '4'])).
% 0.72/0.92  thf('6', plain,
% 0.72/0.92      (![X0 : $i]: (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0))),
% 0.72/0.92      inference('simplify', [status(thm)], ['5'])).
% 0.72/0.92  thf(t26_ordinal1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( v3_ordinal1 @ A ) =>
% 0.72/0.92       ( ![B:$i]:
% 0.72/0.92         ( ( v3_ordinal1 @ B ) =>
% 0.72/0.92           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.72/0.92  thf('7', plain,
% 0.72/0.92      (![X80 : $i, X81 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X80)
% 0.72/0.92          | (r1_ordinal1 @ X81 @ X80)
% 0.72/0.92          | (r2_hidden @ X80 @ X81)
% 0.72/0.92          | ~ (v3_ordinal1 @ X81))),
% 0.72/0.92      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.72/0.92  thf(d2_ordinal1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( v1_ordinal1 @ A ) <=>
% 0.72/0.92       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.72/0.92  thf('8', plain,
% 0.72/0.92      (![X75 : $i, X76 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X75 @ X76)
% 0.72/0.92          | (r1_tarski @ X75 @ X76)
% 0.72/0.92          | ~ (v1_ordinal1 @ X76))),
% 0.72/0.92      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.72/0.92  thf('9', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X0)
% 0.72/0.92          | (r1_ordinal1 @ X0 @ X1)
% 0.72/0.92          | ~ (v3_ordinal1 @ X1)
% 0.72/0.92          | ~ (v1_ordinal1 @ X0)
% 0.72/0.92          | (r1_tarski @ X1 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['7', '8'])).
% 0.72/0.92  thf(d1_enumset1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.92     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.72/0.92       ( ![E:$i]:
% 0.72/0.92         ( ( r2_hidden @ E @ D ) <=>
% 0.72/0.92           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.72/0.92  thf(zf_stmt_1, axiom,
% 0.72/0.92    (![E:$i,C:$i,B:$i,A:$i]:
% 0.72/0.92     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.72/0.92       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.72/0.92  thf('10', plain,
% 0.72/0.92      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.72/0.92         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.72/0.92          | ((X10) = (X11))
% 0.72/0.92          | ((X10) = (X12))
% 0.72/0.92          | ((X10) = (X13)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.72/0.92  thf('11', plain,
% 0.72/0.92      (((r1_ordinal1 @ sk_A @ sk_B_1)
% 0.72/0.92        | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('12', plain,
% 0.72/0.92      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('split', [status(esa)], ['11'])).
% 0.72/0.92  thf(d1_ordinal1, axiom,
% 0.72/0.92    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.72/0.92  thf('13', plain,
% 0.72/0.92      (![X74 : $i]:
% 0.72/0.92         ((k1_ordinal1 @ X74) = (k2_xboole_0 @ X74 @ (k1_tarski @ X74)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.72/0.92  thf(l51_zfmisc_1, axiom,
% 0.72/0.92    (![A:$i,B:$i]:
% 0.72/0.92     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.72/0.92  thf('14', plain,
% 0.72/0.92      (![X49 : $i, X50 : $i]:
% 0.72/0.92         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.72/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.72/0.92  thf('15', plain,
% 0.72/0.92      (![X74 : $i]:
% 0.72/0.92         ((k1_ordinal1 @ X74)
% 0.72/0.92           = (k3_tarski @ (k2_tarski @ X74 @ (k1_tarski @ X74))))),
% 0.72/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.72/0.92  thf(d3_xboole_0, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.72/0.92       ( ![D:$i]:
% 0.72/0.92         ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.92           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.72/0.92  thf('16', plain,
% 0.72/0.92      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X4 @ X2)
% 0.72/0.92          | (r2_hidden @ X4 @ X3)
% 0.72/0.92          | (r2_hidden @ X4 @ X1)
% 0.72/0.92          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.72/0.92  thf('17', plain,
% 0.72/0.92      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.72/0.92         ((r2_hidden @ X4 @ X1)
% 0.72/0.92          | (r2_hidden @ X4 @ X3)
% 0.72/0.92          | ~ (r2_hidden @ X4 @ (k2_xboole_0 @ X3 @ X1)))),
% 0.72/0.92      inference('simplify', [status(thm)], ['16'])).
% 0.72/0.92  thf('18', plain,
% 0.72/0.92      (![X49 : $i, X50 : $i]:
% 0.72/0.92         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.72/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.72/0.92  thf('19', plain,
% 0.72/0.92      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.72/0.92         ((r2_hidden @ X4 @ X1)
% 0.72/0.92          | (r2_hidden @ X4 @ X3)
% 0.72/0.92          | ~ (r2_hidden @ X4 @ (k3_tarski @ (k2_tarski @ X3 @ X1))))),
% 0.72/0.92      inference('demod', [status(thm)], ['17', '18'])).
% 0.72/0.92  thf('20', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.72/0.92          | (r2_hidden @ X1 @ X0)
% 0.72/0.92          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['15', '19'])).
% 0.72/0.92  thf('21', plain,
% 0.72/0.92      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B_1))
% 0.72/0.92         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['12', '20'])).
% 0.72/0.92  thf(t69_enumset1, axiom,
% 0.72/0.92    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.72/0.92  thf('22', plain,
% 0.72/0.92      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.72/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.92  thf(t70_enumset1, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.72/0.92  thf('23', plain,
% 0.72/0.92      (![X22 : $i, X23 : $i]:
% 0.72/0.92         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.72/0.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.72/0.92  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.72/0.92  thf(zf_stmt_3, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.72/0.92     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.72/0.92       ( ![E:$i]:
% 0.72/0.92         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.72/0.92  thf('24', plain,
% 0.72/0.92      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X19 @ X18)
% 0.72/0.92          | ~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.72/0.92          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.72/0.92  thf('25', plain,
% 0.72/0.92      (![X15 : $i, X16 : $i, X17 : $i, X19 : $i]:
% 0.72/0.92         (~ (zip_tseitin_0 @ X19 @ X15 @ X16 @ X17)
% 0.72/0.92          | ~ (r2_hidden @ X19 @ (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.72/0.92      inference('simplify', [status(thm)], ['24'])).
% 0.72/0.92  thf('26', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.72/0.92          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.72/0.92      inference('sup-', [status(thm)], ['23', '25'])).
% 0.72/0.92  thf('27', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.72/0.92          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['22', '26'])).
% 0.72/0.92  thf('28', plain,
% 0.72/0.92      ((((r2_hidden @ sk_A @ sk_B_1)
% 0.72/0.92         | ~ (zip_tseitin_0 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_B_1)))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['21', '27'])).
% 0.72/0.92  thf('29', plain,
% 0.72/0.92      (((((sk_A) = (sk_B_1))
% 0.72/0.92         | ((sk_A) = (sk_B_1))
% 0.72/0.92         | ((sk_A) = (sk_B_1))
% 0.72/0.92         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['10', '28'])).
% 0.72/0.92  thf('30', plain,
% 0.72/0.92      ((((r2_hidden @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('simplify', [status(thm)], ['29'])).
% 0.72/0.92  thf(t7_ordinal1, axiom,
% 0.72/0.92    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.92  thf('31', plain,
% 0.72/0.92      (![X82 : $i, X83 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X82 @ X83) | ~ (r1_tarski @ X83 @ X82))),
% 0.72/0.92      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.72/0.92  thf('32', plain,
% 0.72/0.92      (((((sk_A) = (sk_B_1)) | ~ (r1_tarski @ sk_B_1 @ sk_A)))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['30', '31'])).
% 0.72/0.92  thf('33', plain,
% 0.72/0.92      (((~ (v1_ordinal1 @ sk_A)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_B_1)
% 0.72/0.92         | (r1_ordinal1 @ sk_A @ sk_B_1)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_A)
% 0.72/0.92         | ((sk_A) = (sk_B_1))))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['9', '32'])).
% 0.72/0.92  thf('34', plain, ((v3_ordinal1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf(cc1_ordinal1, axiom,
% 0.72/0.92    (![A:$i]:
% 0.72/0.92     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.72/0.92  thf('35', plain,
% 0.72/0.92      (![X73 : $i]: ((v1_ordinal1 @ X73) | ~ (v3_ordinal1 @ X73))),
% 0.72/0.92      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.72/0.92  thf('36', plain, ((v1_ordinal1 @ sk_A)),
% 0.72/0.92      inference('sup-', [status(thm)], ['34', '35'])).
% 0.72/0.92  thf('37', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('39', plain,
% 0.72/0.92      ((((r1_ordinal1 @ sk_A @ sk_B_1) | ((sk_A) = (sk_B_1))))
% 0.72/0.92         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('demod', [status(thm)], ['33', '36', '37', '38'])).
% 0.72/0.92  thf('40', plain,
% 0.72/0.92      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('41', plain,
% 0.72/0.92      ((((sk_A) = (sk_B_1)))
% 0.72/0.92         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.72/0.92             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['39', '40'])).
% 0.72/0.92  thf('42', plain,
% 0.72/0.92      ((~ (r1_ordinal1 @ sk_A @ sk_B_1)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('43', plain,
% 0.72/0.92      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.72/0.92         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.72/0.92             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['41', '42'])).
% 0.72/0.92  thf('44', plain,
% 0.72/0.92      ((~ (v3_ordinal1 @ sk_A))
% 0.72/0.92         <= (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) & 
% 0.72/0.92             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['6', '43'])).
% 0.72/0.92  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('46', plain,
% 0.72/0.92      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.72/0.92       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.72/0.92  thf('47', plain,
% 0.72/0.92      (((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.72/0.92       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['11'])).
% 0.72/0.92  thf('48', plain,
% 0.72/0.92      (![X74 : $i]:
% 0.72/0.92         ((k1_ordinal1 @ X74)
% 0.72/0.92           = (k3_tarski @ (k2_tarski @ X74 @ (k1_tarski @ X74))))),
% 0.72/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.72/0.92  thf(t71_enumset1, axiom,
% 0.72/0.92    (![A:$i,B:$i,C:$i]:
% 0.72/0.92     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.72/0.92  thf('49', plain,
% 0.72/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.72/0.92         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.72/0.92           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.72/0.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.72/0.92  thf('50', plain,
% 0.72/0.92      (![X22 : $i, X23 : $i]:
% 0.72/0.92         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.72/0.92      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.72/0.92  thf('51', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['49', '50'])).
% 0.72/0.92  thf('52', plain,
% 0.72/0.92      (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.72/0.92      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.72/0.92  thf('53', plain,
% 0.72/0.92      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['51', '52'])).
% 0.72/0.92  thf('54', plain,
% 0.72/0.92      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.72/0.92         ((k2_enumset1 @ X24 @ X24 @ X25 @ X26)
% 0.72/0.92           = (k1_enumset1 @ X24 @ X25 @ X26))),
% 0.72/0.92      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.72/0.92  thf('55', plain,
% 0.72/0.92      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.72/0.92         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.72/0.92          | (r2_hidden @ X14 @ X18)
% 0.72/0.92          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.72/0.92  thf('56', plain,
% 0.72/0.92      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.72/0.92         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.72/0.92          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.72/0.92      inference('simplify', [status(thm)], ['55'])).
% 0.72/0.92  thf('57', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.92         ((r2_hidden @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 0.72/0.92          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2))),
% 0.72/0.92      inference('sup+', [status(thm)], ['54', '56'])).
% 0.72/0.92  thf('58', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.72/0.92          | (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['53', '57'])).
% 0.72/0.92  thf('59', plain,
% 0.72/0.92      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.72/0.92         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.72/0.92  thf('60', plain,
% 0.72/0.92      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.72/0.92      inference('simplify', [status(thm)], ['59'])).
% 0.72/0.92  thf('61', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.72/0.92      inference('sup-', [status(thm)], ['58', '60'])).
% 0.72/0.92  thf('62', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X0 @ X1)
% 0.72/0.92          | (r2_hidden @ X0 @ X2)
% 0.72/0.92          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.72/0.92  thf('63', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.72/0.92         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.72/0.92      inference('simplify', [status(thm)], ['62'])).
% 0.72/0.92  thf('64', plain,
% 0.72/0.92      (![X49 : $i, X50 : $i]:
% 0.72/0.92         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.72/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.72/0.92  thf('65', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.72/0.92         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.72/0.92          | ~ (r2_hidden @ X0 @ X1))),
% 0.72/0.92      inference('demod', [status(thm)], ['63', '64'])).
% 0.72/0.92  thf('66', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         (r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ (k1_tarski @ X0))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['61', '65'])).
% 0.72/0.92  thf('67', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['48', '66'])).
% 0.72/0.92  thf('68', plain,
% 0.72/0.92      (![X74 : $i]:
% 0.72/0.92         ((k1_ordinal1 @ X74)
% 0.72/0.92           = (k3_tarski @ (k2_tarski @ X74 @ (k1_tarski @ X74))))),
% 0.72/0.92      inference('demod', [status(thm)], ['13', '14'])).
% 0.72/0.92  thf('69', plain,
% 0.72/0.92      (![X80 : $i, X81 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X80)
% 0.72/0.92          | (r1_ordinal1 @ X81 @ X80)
% 0.72/0.92          | (r2_hidden @ X80 @ X81)
% 0.72/0.92          | ~ (v3_ordinal1 @ X81))),
% 0.72/0.92      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.72/0.92  thf('70', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.72/0.92         (~ (r2_hidden @ X0 @ X3)
% 0.72/0.92          | (r2_hidden @ X0 @ X2)
% 0.72/0.92          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.72/0.92      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.72/0.92  thf('71', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.72/0.92         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.72/0.92      inference('simplify', [status(thm)], ['70'])).
% 0.72/0.92  thf('72', plain,
% 0.72/0.92      (![X49 : $i, X50 : $i]:
% 0.72/0.92         ((k3_tarski @ (k2_tarski @ X49 @ X50)) = (k2_xboole_0 @ X49 @ X50))),
% 0.72/0.92      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.72/0.92  thf('73', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.72/0.92         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.72/0.92          | ~ (r2_hidden @ X0 @ X3))),
% 0.72/0.92      inference('demod', [status(thm)], ['71', '72'])).
% 0.72/0.92  thf('74', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X0)
% 0.72/0.92          | (r1_ordinal1 @ X0 @ X1)
% 0.72/0.92          | ~ (v3_ordinal1 @ X1)
% 0.72/0.92          | (r2_hidden @ X1 @ (k3_tarski @ (k2_tarski @ X0 @ X2))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['69', '73'])).
% 0.72/0.92  thf('75', plain,
% 0.72/0.92      (![X0 : $i, X1 : $i]:
% 0.72/0.92         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.72/0.92          | ~ (v3_ordinal1 @ X1)
% 0.72/0.92          | (r1_ordinal1 @ X0 @ X1)
% 0.72/0.92          | ~ (v3_ordinal1 @ X0))),
% 0.72/0.92      inference('sup+', [status(thm)], ['68', '74'])).
% 0.72/0.92  thf('76', plain,
% 0.72/0.92      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('77', plain,
% 0.72/0.92      (((~ (v3_ordinal1 @ sk_B_1)
% 0.72/0.92         | (r1_ordinal1 @ sk_B_1 @ sk_A)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_A)))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['75', '76'])).
% 0.72/0.92  thf('78', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('79', plain, ((v3_ordinal1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('80', plain,
% 0.72/0.92      (((r1_ordinal1 @ sk_B_1 @ sk_A))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.72/0.92  thf('81', plain,
% 0.72/0.92      (![X78 : $i, X79 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X78)
% 0.72/0.92          | ~ (v3_ordinal1 @ X79)
% 0.72/0.92          | (r1_tarski @ X78 @ X79)
% 0.72/0.92          | ~ (r1_ordinal1 @ X78 @ X79))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.72/0.92  thf('82', plain,
% 0.72/0.92      ((((r1_tarski @ sk_B_1 @ sk_A)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_A)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_B_1)))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('sup-', [status(thm)], ['80', '81'])).
% 0.72/0.92  thf('83', plain, ((v3_ordinal1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('84', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('85', plain,
% 0.72/0.92      (((r1_tarski @ sk_B_1 @ sk_A))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.72/0.92  thf('86', plain,
% 0.72/0.92      (((r1_ordinal1 @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('split', [status(esa)], ['11'])).
% 0.72/0.92  thf('87', plain,
% 0.72/0.92      (![X78 : $i, X79 : $i]:
% 0.72/0.92         (~ (v3_ordinal1 @ X78)
% 0.72/0.92          | ~ (v3_ordinal1 @ X79)
% 0.72/0.92          | (r1_tarski @ X78 @ X79)
% 0.72/0.92          | ~ (r1_ordinal1 @ X78 @ X79))),
% 0.72/0.92      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.72/0.92  thf('88', plain,
% 0.72/0.92      ((((r1_tarski @ sk_A @ sk_B_1)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_B_1)
% 0.72/0.92         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['86', '87'])).
% 0.72/0.92  thf('89', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('90', plain, ((v3_ordinal1 @ sk_A)),
% 0.72/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.92  thf('91', plain,
% 0.72/0.92      (((r1_tarski @ sk_A @ sk_B_1)) <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.72/0.92  thf('92', plain,
% 0.72/0.92      (![X6 : $i, X8 : $i]:
% 0.72/0.92         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.72/0.92      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.92  thf('93', plain,
% 0.72/0.92      (((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) = (sk_A))))
% 0.72/0.92         <= (((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['91', '92'])).
% 0.72/0.92  thf('94', plain,
% 0.72/0.92      ((((sk_B_1) = (sk_A)))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.72/0.92             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['85', '93'])).
% 0.72/0.92  thf('95', plain,
% 0.72/0.92      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))))),
% 0.72/0.92      inference('split', [status(esa)], ['0'])).
% 0.72/0.92  thf('96', plain,
% 0.72/0.92      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.72/0.92         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1))) & 
% 0.72/0.92             ((r1_ordinal1 @ sk_A @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['94', '95'])).
% 0.72/0.92  thf('97', plain,
% 0.72/0.92      (~ ((r1_ordinal1 @ sk_A @ sk_B_1)) | 
% 0.72/0.92       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B_1)))),
% 0.72/0.92      inference('sup-', [status(thm)], ['67', '96'])).
% 0.72/0.92  thf('98', plain, ($false),
% 0.72/0.92      inference('sat_resolution*', [status(thm)], ['1', '46', '47', '97'])).
% 0.72/0.92  
% 0.72/0.92  % SZS output end Refutation
% 0.72/0.92  
% 0.72/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
