%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UAtzw2Yi3J

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:03 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 245 expanded)
%              Number of leaves         :   20 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  741 (2053 expanded)
%              Number of equality atoms :   35 (  65 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k1_ordinal1 @ X17 )
      = ( k2_xboole_0 @ X17 @ ( k1_tarski @ X17 ) ) ) ),
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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('17',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('22',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

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
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('30',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( k1_ordinal1 @ X17 )
      = ( k2_xboole_0 @ X17 @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( r1_ordinal1 @ X23 @ X22 )
      | ( r2_hidden @ X22 @ X23 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('34',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('35',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('39',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X19 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_ordinal1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('44',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v3_ordinal1 @ X18 )
      | ~ ( v3_ordinal1 @ X19 )
      | ( r1_tarski @ X18 @ X19 )
      | ~ ( r1_ordinal1 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('50',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v3_ordinal1 @ X20 )
      | ( r2_hidden @ X21 @ X20 )
      | ( X21 = X20 )
      | ( r2_hidden @ X20 @ X21 )
      | ~ ( v3_ordinal1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('55',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('62',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['47','62'])).

thf('64',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['26'])).

thf('65',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X17: $i] :
      ( ( k1_ordinal1 @ X17 )
      = ( k2_xboole_0 @ X17 @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('67',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('68',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('69',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['67','69'])).

thf('71',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('72',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['65','74'])).

thf('76',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','75'])).

thf('77',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
    | ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('78',plain,(
    r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['31','75','77'])).

thf('79',plain,(
    ~ ( r1_ordinal1 @ sk_A @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','76','78'])).

thf('80',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','79'])).

thf('81',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UAtzw2Yi3J
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 1.51/1.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.70  % Solved by: fo/fo7.sh
% 1.51/1.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.70  % done 3072 iterations in 1.255s
% 1.51/1.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.70  % SZS output start Refutation
% 1.51/1.70  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 1.51/1.70  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 1.51/1.70  thf(sk_B_type, type, sk_B: $i).
% 1.51/1.70  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.70  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.51/1.70  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 1.51/1.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.51/1.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.51/1.70  thf(t26_ordinal1, axiom,
% 1.51/1.70    (![A:$i]:
% 1.51/1.70     ( ( v3_ordinal1 @ A ) =>
% 1.51/1.70       ( ![B:$i]:
% 1.51/1.70         ( ( v3_ordinal1 @ B ) =>
% 1.51/1.70           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 1.51/1.70  thf('0', plain,
% 1.51/1.70      (![X22 : $i, X23 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X22)
% 1.51/1.70          | (r1_ordinal1 @ X23 @ X22)
% 1.51/1.70          | (r2_hidden @ X22 @ X23)
% 1.51/1.70          | ~ (v3_ordinal1 @ X23))),
% 1.51/1.70      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.51/1.70  thf('1', plain,
% 1.51/1.70      (![X22 : $i, X23 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X22)
% 1.51/1.70          | (r1_ordinal1 @ X23 @ X22)
% 1.51/1.70          | (r2_hidden @ X22 @ X23)
% 1.51/1.70          | ~ (v3_ordinal1 @ X23))),
% 1.51/1.70      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.51/1.70  thf(antisymmetry_r2_hidden, axiom,
% 1.51/1.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 1.51/1.70  thf('2', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 1.51/1.70      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 1.51/1.70  thf('3', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X0)
% 1.51/1.70          | (r1_ordinal1 @ X0 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X1)
% 1.51/1.70          | ~ (r2_hidden @ X0 @ X1))),
% 1.51/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.51/1.70  thf('4', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X0)
% 1.51/1.70          | (r1_ordinal1 @ X0 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X0)
% 1.51/1.70          | (r1_ordinal1 @ X1 @ X0)
% 1.51/1.70          | ~ (v3_ordinal1 @ X1))),
% 1.51/1.70      inference('sup-', [status(thm)], ['0', '3'])).
% 1.51/1.70  thf('5', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         ((r1_ordinal1 @ X1 @ X0)
% 1.51/1.70          | ~ (v3_ordinal1 @ X1)
% 1.51/1.70          | (r1_ordinal1 @ X0 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X0))),
% 1.51/1.70      inference('simplify', [status(thm)], ['4'])).
% 1.51/1.70  thf('6', plain,
% 1.51/1.70      (![X0 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 1.51/1.70      inference('eq_fact', [status(thm)], ['5'])).
% 1.51/1.70  thf('7', plain,
% 1.51/1.70      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 1.51/1.70      inference('simplify', [status(thm)], ['6'])).
% 1.51/1.70  thf(t34_ordinal1, conjecture,
% 1.51/1.70    (![A:$i]:
% 1.51/1.70     ( ( v3_ordinal1 @ A ) =>
% 1.51/1.70       ( ![B:$i]:
% 1.51/1.70         ( ( v3_ordinal1 @ B ) =>
% 1.51/1.70           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.51/1.70             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 1.51/1.70  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.70    (~( ![A:$i]:
% 1.51/1.70        ( ( v3_ordinal1 @ A ) =>
% 1.51/1.70          ( ![B:$i]:
% 1.51/1.70            ( ( v3_ordinal1 @ B ) =>
% 1.51/1.70              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 1.51/1.70                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 1.51/1.70    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 1.51/1.70  thf('8', plain,
% 1.51/1.70      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('9', plain,
% 1.51/1.70      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.51/1.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('split', [status(esa)], ['8'])).
% 1.51/1.70  thf(d1_ordinal1, axiom,
% 1.51/1.70    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 1.51/1.70  thf('10', plain,
% 1.51/1.70      (![X17 : $i]:
% 1.51/1.70         ((k1_ordinal1 @ X17) = (k2_xboole_0 @ X17 @ (k1_tarski @ X17)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.51/1.70  thf(d3_xboole_0, axiom,
% 1.51/1.70    (![A:$i,B:$i,C:$i]:
% 1.51/1.70     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.51/1.70       ( ![D:$i]:
% 1.51/1.70         ( ( r2_hidden @ D @ C ) <=>
% 1.51/1.70           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.51/1.70  thf('11', plain,
% 1.51/1.70      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X6 @ X4)
% 1.51/1.70          | (r2_hidden @ X6 @ X5)
% 1.51/1.70          | (r2_hidden @ X6 @ X3)
% 1.51/1.70          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.51/1.70  thf('12', plain,
% 1.51/1.70      (![X3 : $i, X5 : $i, X6 : $i]:
% 1.51/1.70         ((r2_hidden @ X6 @ X3)
% 1.51/1.70          | (r2_hidden @ X6 @ X5)
% 1.51/1.70          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 1.51/1.70      inference('simplify', [status(thm)], ['11'])).
% 1.51/1.70  thf('13', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.51/1.70          | (r2_hidden @ X1 @ X0)
% 1.51/1.70          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['10', '12'])).
% 1.51/1.70  thf('14', plain,
% 1.51/1.70      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['9', '13'])).
% 1.51/1.70  thf(t69_enumset1, axiom,
% 1.51/1.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.51/1.70  thf('15', plain,
% 1.51/1.70      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.51/1.70  thf(d2_tarski, axiom,
% 1.51/1.70    (![A:$i,B:$i,C:$i]:
% 1.51/1.70     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 1.51/1.70       ( ![D:$i]:
% 1.51/1.70         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 1.51/1.70  thf('16', plain,
% 1.51/1.70      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X12 @ X10)
% 1.51/1.70          | ((X12) = (X11))
% 1.51/1.70          | ((X12) = (X8))
% 1.51/1.70          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d2_tarski])).
% 1.51/1.70  thf('17', plain,
% 1.51/1.70      (![X8 : $i, X11 : $i, X12 : $i]:
% 1.51/1.70         (((X12) = (X8))
% 1.51/1.70          | ((X12) = (X11))
% 1.51/1.70          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 1.51/1.70      inference('simplify', [status(thm)], ['16'])).
% 1.51/1.70  thf('18', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['15', '17'])).
% 1.51/1.70  thf('19', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 1.51/1.70      inference('simplify', [status(thm)], ['18'])).
% 1.51/1.70  thf('20', plain,
% 1.51/1.70      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 1.51/1.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['14', '19'])).
% 1.51/1.70  thf('21', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X0)
% 1.51/1.70          | (r1_ordinal1 @ X0 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X1)
% 1.51/1.70          | ~ (r2_hidden @ X0 @ X1))),
% 1.51/1.70      inference('sup-', [status(thm)], ['1', '2'])).
% 1.51/1.70  thf('22', plain,
% 1.51/1.70      (((((sk_A) = (sk_B))
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_B)
% 1.51/1.70         | (r1_ordinal1 @ sk_A @ sk_B)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_A)))
% 1.51/1.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['20', '21'])).
% 1.51/1.70  thf('23', plain, ((v3_ordinal1 @ sk_B)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('24', plain, ((v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('25', plain,
% 1.51/1.70      (((((sk_A) = (sk_B)) | (r1_ordinal1 @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.51/1.70  thf('26', plain,
% 1.51/1.70      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 1.51/1.70        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('27', plain,
% 1.51/1.70      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('split', [status(esa)], ['26'])).
% 1.51/1.70  thf('28', plain,
% 1.51/1.70      ((((sk_A) = (sk_B)))
% 1.51/1.70         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.51/1.70             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['25', '27'])).
% 1.51/1.70  thf('29', plain,
% 1.51/1.70      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('split', [status(esa)], ['26'])).
% 1.51/1.70  thf('30', plain,
% 1.51/1.70      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 1.51/1.70         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 1.51/1.70             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['28', '29'])).
% 1.51/1.70  thf('31', plain,
% 1.51/1.70      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 1.51/1.70       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.51/1.70      inference('split', [status(esa)], ['26'])).
% 1.51/1.70  thf('32', plain,
% 1.51/1.70      (![X17 : $i]:
% 1.51/1.70         ((k1_ordinal1 @ X17) = (k2_xboole_0 @ X17 @ (k1_tarski @ X17)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.51/1.70  thf('33', plain,
% 1.51/1.70      (![X22 : $i, X23 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X22)
% 1.51/1.70          | (r1_ordinal1 @ X23 @ X22)
% 1.51/1.70          | (r2_hidden @ X22 @ X23)
% 1.51/1.70          | ~ (v3_ordinal1 @ X23))),
% 1.51/1.70      inference('cnf', [status(esa)], [t26_ordinal1])).
% 1.51/1.70  thf('34', plain,
% 1.51/1.70      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X2 @ X5)
% 1.51/1.70          | (r2_hidden @ X2 @ X4)
% 1.51/1.70          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.51/1.70  thf('35', plain,
% 1.51/1.70      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.51/1.70         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 1.51/1.70      inference('simplify', [status(thm)], ['34'])).
% 1.51/1.70  thf('36', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X0)
% 1.51/1.70          | (r1_ordinal1 @ X0 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X1)
% 1.51/1.70          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['33', '35'])).
% 1.51/1.70  thf('37', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 1.51/1.70          | ~ (v3_ordinal1 @ X1)
% 1.51/1.70          | (r1_ordinal1 @ X0 @ X1)
% 1.51/1.70          | ~ (v3_ordinal1 @ X0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['32', '36'])).
% 1.51/1.70  thf('38', plain,
% 1.51/1.70      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('split', [status(esa)], ['26'])).
% 1.51/1.70  thf('39', plain,
% 1.51/1.70      (((~ (v3_ordinal1 @ sk_B)
% 1.51/1.70         | (r1_ordinal1 @ sk_B @ sk_A)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_A)))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['37', '38'])).
% 1.51/1.70  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('41', plain, ((v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('42', plain,
% 1.51/1.70      (((r1_ordinal1 @ sk_B @ sk_A))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.51/1.70  thf(redefinition_r1_ordinal1, axiom,
% 1.51/1.70    (![A:$i,B:$i]:
% 1.51/1.70     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 1.51/1.70       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 1.51/1.70  thf('43', plain,
% 1.51/1.70      (![X18 : $i, X19 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X18)
% 1.51/1.70          | ~ (v3_ordinal1 @ X19)
% 1.51/1.70          | (r1_tarski @ X18 @ X19)
% 1.51/1.70          | ~ (r1_ordinal1 @ X18 @ X19))),
% 1.51/1.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.51/1.70  thf('44', plain,
% 1.51/1.70      ((((r1_tarski @ sk_B @ sk_A)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_A)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_B)))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('sup-', [status(thm)], ['42', '43'])).
% 1.51/1.70  thf('45', plain, ((v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('46', plain, ((v3_ordinal1 @ sk_B)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('47', plain,
% 1.51/1.70      (((r1_tarski @ sk_B @ sk_A))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('demod', [status(thm)], ['44', '45', '46'])).
% 1.51/1.70  thf('48', plain,
% 1.51/1.70      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('split', [status(esa)], ['8'])).
% 1.51/1.70  thf('49', plain,
% 1.51/1.70      (![X18 : $i, X19 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X18)
% 1.51/1.70          | ~ (v3_ordinal1 @ X19)
% 1.51/1.70          | (r1_tarski @ X18 @ X19)
% 1.51/1.70          | ~ (r1_ordinal1 @ X18 @ X19))),
% 1.51/1.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 1.51/1.70  thf('50', plain,
% 1.51/1.70      ((((r1_tarski @ sk_A @ sk_B)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_B)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['48', '49'])).
% 1.51/1.70  thf('51', plain, ((v3_ordinal1 @ sk_B)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('52', plain, ((v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('53', plain,
% 1.51/1.70      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.51/1.70  thf(t24_ordinal1, axiom,
% 1.51/1.70    (![A:$i]:
% 1.51/1.70     ( ( v3_ordinal1 @ A ) =>
% 1.51/1.70       ( ![B:$i]:
% 1.51/1.70         ( ( v3_ordinal1 @ B ) =>
% 1.51/1.70           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 1.51/1.70                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 1.51/1.70  thf('54', plain,
% 1.51/1.70      (![X20 : $i, X21 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X20)
% 1.51/1.70          | (r2_hidden @ X21 @ X20)
% 1.51/1.70          | ((X21) = (X20))
% 1.51/1.70          | (r2_hidden @ X20 @ X21)
% 1.51/1.70          | ~ (v3_ordinal1 @ X21))),
% 1.51/1.70      inference('cnf', [status(esa)], [t24_ordinal1])).
% 1.51/1.70  thf(t7_ordinal1, axiom,
% 1.51/1.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.51/1.70  thf('55', plain,
% 1.51/1.70      (![X24 : $i, X25 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 1.51/1.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.51/1.70  thf('56', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (~ (v3_ordinal1 @ X1)
% 1.51/1.70          | (r2_hidden @ X0 @ X1)
% 1.51/1.70          | ((X1) = (X0))
% 1.51/1.70          | ~ (v3_ordinal1 @ X0)
% 1.51/1.70          | ~ (r1_tarski @ X0 @ X1))),
% 1.51/1.70      inference('sup-', [status(thm)], ['54', '55'])).
% 1.51/1.70  thf('57', plain,
% 1.51/1.70      (((~ (v3_ordinal1 @ sk_A)
% 1.51/1.70         | ((sk_B) = (sk_A))
% 1.51/1.70         | (r2_hidden @ sk_A @ sk_B)
% 1.51/1.70         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['53', '56'])).
% 1.51/1.70  thf('58', plain, ((v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('59', plain, ((v3_ordinal1 @ sk_B)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('60', plain,
% 1.51/1.70      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 1.51/1.70         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('demod', [status(thm)], ['57', '58', '59'])).
% 1.51/1.70  thf('61', plain,
% 1.51/1.70      (![X24 : $i, X25 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 1.51/1.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.51/1.70  thf('62', plain,
% 1.51/1.70      (((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 1.51/1.70         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['60', '61'])).
% 1.51/1.70  thf('63', plain,
% 1.51/1.70      ((((sk_B) = (sk_A)))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.51/1.70             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['47', '62'])).
% 1.51/1.70  thf('64', plain,
% 1.51/1.70      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 1.51/1.70      inference('split', [status(esa)], ['26'])).
% 1.51/1.70  thf('65', plain,
% 1.51/1.70      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 1.51/1.70         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 1.51/1.70             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['63', '64'])).
% 1.51/1.70  thf('66', plain,
% 1.51/1.70      (![X17 : $i]:
% 1.51/1.70         ((k1_ordinal1 @ X17) = (k2_xboole_0 @ X17 @ (k1_tarski @ X17)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d1_ordinal1])).
% 1.51/1.70  thf('67', plain,
% 1.51/1.70      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 1.51/1.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.51/1.70  thf('68', plain,
% 1.51/1.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.51/1.70         (((X9) != (X8))
% 1.51/1.70          | (r2_hidden @ X9 @ X10)
% 1.51/1.70          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d2_tarski])).
% 1.51/1.70  thf('69', plain,
% 1.51/1.70      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 1.51/1.70      inference('simplify', [status(thm)], ['68'])).
% 1.51/1.70  thf('70', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['67', '69'])).
% 1.51/1.70  thf('71', plain,
% 1.51/1.70      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.70         (~ (r2_hidden @ X2 @ X3)
% 1.51/1.70          | (r2_hidden @ X2 @ X4)
% 1.51/1.70          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.51/1.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.51/1.70  thf('72', plain,
% 1.51/1.70      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.51/1.70         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 1.51/1.70      inference('simplify', [status(thm)], ['71'])).
% 1.51/1.70  thf('73', plain,
% 1.51/1.70      (![X0 : $i, X1 : $i]:
% 1.51/1.70         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.51/1.70      inference('sup-', [status(thm)], ['70', '72'])).
% 1.51/1.70  thf('74', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 1.51/1.70      inference('sup+', [status(thm)], ['66', '73'])).
% 1.51/1.70  thf('75', plain,
% 1.51/1.70      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 1.51/1.70       ~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 1.51/1.70      inference('demod', [status(thm)], ['65', '74'])).
% 1.51/1.70  thf('76', plain, (~ ((r1_ordinal1 @ sk_A @ sk_B))),
% 1.51/1.70      inference('sat_resolution*', [status(thm)], ['31', '75'])).
% 1.51/1.70  thf('77', plain,
% 1.51/1.70      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) | 
% 1.51/1.70       ((r1_ordinal1 @ sk_A @ sk_B))),
% 1.51/1.70      inference('split', [status(esa)], ['8'])).
% 1.51/1.70  thf('78', plain, (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 1.51/1.70      inference('sat_resolution*', [status(thm)], ['31', '75', '77'])).
% 1.51/1.70  thf('79', plain, (~ (r1_ordinal1 @ sk_A @ sk_A)),
% 1.51/1.70      inference('simpl_trail', [status(thm)], ['30', '76', '78'])).
% 1.51/1.70  thf('80', plain, (~ (v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('sup-', [status(thm)], ['7', '79'])).
% 1.51/1.70  thf('81', plain, ((v3_ordinal1 @ sk_A)),
% 1.51/1.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.70  thf('82', plain, ($false), inference('demod', [status(thm)], ['80', '81'])).
% 1.51/1.70  
% 1.51/1.70  % SZS output end Refutation
% 1.51/1.70  
% 1.51/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
