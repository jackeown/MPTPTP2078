%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VtPFzxRQY7

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 161 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   15
%              Number of atoms          :  669 (1457 expanded)
%              Number of equality atoms :   54 ( 119 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('17',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k11_relat_1 @ X19 @ X20 )
        = ( k9_relat_1 @ X19 @ ( k1_tarski @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k9_relat_1 @ X33 @ X34 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('25',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['16'])).

thf('28',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
      & ( ( k11_relat_1 @ sk_B_2 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( k2_tarski @ X16 @ X16 )
      = ( k1_tarski @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_enumset1 @ X17 @ X17 @ X18 )
      = ( k2_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) )
    | ( ( k11_relat_1 @ sk_B_2 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('42',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['17','40','41'])).

thf('43',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['15','42'])).

thf('44',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B_2 ) @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X33 ) @ X34 )
      | ( ( k9_relat_1 @ X33 @ X34 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_B_2 )
    | ( ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('56',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k11_relat_1 @ X19 @ X20 )
        = ( k9_relat_1 @ X19 @ ( k1_tarski @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_B_2 @ X0 )
      = ( k9_relat_1 @ sk_B_2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k11_relat_1 @ sk_B_2 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['53','54','57'])).

thf('59',plain,
    ( ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_2 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('60',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['17','40'])).

thf('61',plain,(
    ( k11_relat_1 @ sk_B_2 @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VtPFzxRQY7
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:21:37 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 275 iterations in 0.156s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.59  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.59  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.59  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.22/0.59  thf(d1_enumset1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.59       ( ![E:$i]:
% 0.22/0.59         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.59           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, axiom,
% 0.22/0.59    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.59     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.59       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.59  thf('0', plain,
% 0.22/0.59      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.59         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.22/0.59          | ((X5) = (X6))
% 0.22/0.59          | ((X5) = (X7))
% 0.22/0.59          | ((X5) = (X8)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t3_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.59  thf(t69_enumset1, axiom,
% 0.22/0.59    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.59  thf('2', plain, (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.59  thf(t70_enumset1, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i]:
% 0.22/0.59         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.59  thf(zf_stmt_2, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.59     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.59       ( ![E:$i]:
% 0.22/0.59         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X14 @ X13)
% 0.22/0.59          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.22/0.59          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.22/0.59         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.22/0.59          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.59      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.59          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.22/0.59          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['2', '6'])).
% 0.22/0.59  thf('8', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.59          | ~ (zip_tseitin_0 @ (sk_C @ X1 @ (k1_tarski @ X0)) @ X0 @ X0 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['1', '7'])).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.22/0.59          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.22/0.59          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0))
% 0.22/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['0', '8'])).
% 0.22/0.59  thf('10', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.59          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.59      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r2_hidden @ X0 @ X1)
% 0.22/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.22/0.59          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.22/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.59  thf('13', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.22/0.59      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.59  thf(t205_relat_1, conjecture,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( v1_relat_1 @ B ) =>
% 0.22/0.59       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.59         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_3, negated_conjecture,
% 0.22/0.59    (~( ![A:$i,B:$i]:
% 0.22/0.59        ( ( v1_relat_1 @ B ) =>
% 0.22/0.59          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.22/0.59            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))
% 0.22/0.59        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.59  thf('15', plain,
% 0.22/0.59      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.22/0.59         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.22/0.59      inference('split', [status(esa)], ['14'])).
% 0.22/0.59  thf('16', plain,
% 0.22/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))
% 0.22/0.59        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.59       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.22/0.59      inference('split', [status(esa)], ['16'])).
% 0.22/0.59  thf('18', plain,
% 0.22/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))
% 0.22/0.59         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['14'])).
% 0.22/0.59  thf(d16_relat_1, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ( v1_relat_1 @ A ) =>
% 0.22/0.59       ( ![B:$i]:
% 0.22/0.59         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.22/0.59  thf('19', plain,
% 0.22/0.59      (![X19 : $i, X20 : $i]:
% 0.22/0.59         (((k11_relat_1 @ X19 @ X20) = (k9_relat_1 @ X19 @ (k1_tarski @ X20)))
% 0.22/0.59          | ~ (v1_relat_1 @ X19))),
% 0.22/0.59      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.59  thf(t151_relat_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( v1_relat_1 @ B ) =>
% 0.22/0.59       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.59         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.59  thf('20', plain,
% 0.22/0.59      (![X33 : $i, X34 : $i]:
% 0.22/0.59         (((k9_relat_1 @ X33 @ X34) != (k1_xboole_0))
% 0.22/0.59          | (r1_xboole_0 @ (k1_relat_1 @ X33) @ X34)
% 0.22/0.59          | ~ (v1_relat_1 @ X33))),
% 0.22/0.59      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.22/0.59          | ~ (v1_relat_1 @ X1)
% 0.22/0.59          | ~ (v1_relat_1 @ X1)
% 0.22/0.59          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.22/0.59          | ~ (v1_relat_1 @ X1)
% 0.22/0.59          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.22/0.59      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.59         | ~ (v1_relat_1 @ sk_B_2)
% 0.22/0.59         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ (k1_tarski @ sk_A))))
% 0.22/0.59         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['18', '22'])).
% 0.22/0.59  thf('24', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      (((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.59         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ (k1_tarski @ sk_A))))
% 0.22/0.59         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.59      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.59  thf('26', plain,
% 0.22/0.59      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ (k1_tarski @ sk_A)))
% 0.22/0.59         <= ((((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.59      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))
% 0.22/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.22/0.59      inference('split', [status(esa)], ['16'])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.59          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.59  thf('29', plain,
% 0.22/0.59      ((![X0 : $i]:
% 0.22/0.59          (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ X0)
% 0.22/0.59           | ~ (r2_hidden @ sk_A @ X0)))
% 0.22/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.22/0.59         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) & 
% 0.22/0.59             (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.59      inference('sup-', [status(thm)], ['26', '29'])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      (![X16 : $i]: ((k2_tarski @ X16 @ X16) = (k1_tarski @ X16))),
% 0.22/0.59      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      (![X17 : $i, X18 : $i]:
% 0.22/0.59         ((k1_enumset1 @ X17 @ X17 @ X18) = (k2_tarski @ X17 @ X18))),
% 0.22/0.59      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.59  thf('33', plain,
% 0.22/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.59         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.22/0.59          | (r2_hidden @ X9 @ X13)
% 0.22/0.59          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.59         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.22/0.59          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.22/0.59      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.59          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.59      inference('sup+', [status(thm)], ['32', '34'])).
% 0.22/0.59  thf('36', plain,
% 0.22/0.59      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.59         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('37', plain,
% 0.22/0.59      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.22/0.59      inference('simplify', [status(thm)], ['36'])).
% 0.22/0.59  thf('38', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['35', '37'])).
% 0.22/0.59  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['31', '38'])).
% 0.22/0.59  thf('40', plain,
% 0.22/0.59      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.22/0.59       ~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.59      inference('demod', [status(thm)], ['30', '39'])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))) | 
% 0.22/0.59       (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.59      inference('split', [status(esa)], ['14'])).
% 0.22/0.59  thf('42', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2)))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)], ['17', '40', '41'])).
% 0.22/0.59  thf('43', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_2))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['15', '42'])).
% 0.22/0.59  thf('44', plain,
% 0.22/0.59      ((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B_2))),
% 0.22/0.59      inference('sup-', [status(thm)], ['13', '43'])).
% 0.22/0.59  thf('45', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.59  thf('46', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.59  thf('47', plain,
% 0.22/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X2 @ X0)
% 0.22/0.59          | ~ (r2_hidden @ X2 @ X3)
% 0.22/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.59  thf('48', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.59          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.59          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.59  thf('49', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.59          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.22/0.59          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['45', '48'])).
% 0.22/0.59  thf('50', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.59  thf('51', plain,
% 0.22/0.59      ((r1_xboole_0 @ (k1_relat_1 @ sk_B_2) @ (k1_tarski @ sk_A))),
% 0.22/0.59      inference('sup-', [status(thm)], ['44', '50'])).
% 0.22/0.59  thf('52', plain,
% 0.22/0.59      (![X33 : $i, X34 : $i]:
% 0.22/0.59         (~ (r1_xboole_0 @ (k1_relat_1 @ X33) @ X34)
% 0.22/0.59          | ((k9_relat_1 @ X33 @ X34) = (k1_xboole_0))
% 0.22/0.59          | ~ (v1_relat_1 @ X33))),
% 0.22/0.59      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.22/0.59  thf('53', plain,
% 0.22/0.59      ((~ (v1_relat_1 @ sk_B_2)
% 0.22/0.59        | ((k9_relat_1 @ sk_B_2 @ (k1_tarski @ sk_A)) = (k1_xboole_0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.22/0.59  thf('54', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.59  thf('55', plain, ((v1_relat_1 @ sk_B_2)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.59  thf('56', plain,
% 0.22/0.59      (![X19 : $i, X20 : $i]:
% 0.22/0.59         (((k11_relat_1 @ X19 @ X20) = (k9_relat_1 @ X19 @ (k1_tarski @ X20)))
% 0.22/0.59          | ~ (v1_relat_1 @ X19))),
% 0.22/0.59      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.22/0.59  thf('57', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k11_relat_1 @ sk_B_2 @ X0)
% 0.22/0.59           = (k9_relat_1 @ sk_B_2 @ (k1_tarski @ X0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.59  thf('58', plain, (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))),
% 0.22/0.59      inference('demod', [status(thm)], ['53', '54', '57'])).
% 0.22/0.59  thf('59', plain,
% 0.22/0.59      ((((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0)))
% 0.22/0.59         <= (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.59      inference('split', [status(esa)], ['16'])).
% 0.22/0.59  thf('60', plain, (~ (((k11_relat_1 @ sk_B_2 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.59      inference('sat_resolution*', [status(thm)], ['17', '40'])).
% 0.22/0.59  thf('61', plain, (((k11_relat_1 @ sk_B_2 @ sk_A) != (k1_xboole_0))),
% 0.22/0.59      inference('simpl_trail', [status(thm)], ['59', '60'])).
% 0.22/0.59  thf('62', plain, ($false),
% 0.22/0.59      inference('simplify_reflect-', [status(thm)], ['58', '61'])).
% 0.22/0.59  
% 0.22/0.59  % SZS output end Refutation
% 0.22/0.59  
% 0.44/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
