%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2P7aQQ1tB0

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:03 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 163 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  750 (1334 expanded)
%              Number of equality atoms :   35 (  50 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( r1_ordinal1 @ X24 @ X23 )
      | ( r2_hidden @ X23 @ X24 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X8 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('7',plain,(
    ! [X8: $i,X11: $i] :
      ( r2_hidden @ X8 @ ( k2_tarski @ X11 @ X8 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ X0 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( k1_ordinal1 @ X18 )
      = ( k2_xboole_0 @ X18 @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('17',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,
    ( ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X14: $i] :
      ( ( k2_tarski @ X14 @ X14 )
      = ( k1_tarski @ X14 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,(
    ! [X8: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ( X12 = X11 )
      | ( X12 = X8 )
      | ( X10
       != ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X8: $i,X11: $i,X12: $i] :
      ( ( X12 = X8 )
      | ( X12 = X11 )
      | ~ ( r2_hidden @ X12 @ ( k2_tarski @ X11 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( ( r2_hidden @ sk_A @ sk_B )
      | ( sk_A = sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( r1_ordinal1 @ X24 @ X23 )
      | ( r2_hidden @ X23 @ X24 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( sk_A = sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( sk_A = sk_B )
      | ( r1_ordinal1 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
   <= ~ ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
   <= ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
      & ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['13'])).

thf('41',plain,(
    ! [X18: $i] :
      ( ( k1_ordinal1 @ X18 )
      = ( k2_xboole_0 @ X18 @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v3_ordinal1 @ X23 )
      | ( r1_ordinal1 @ X24 @ X23 )
      | ( r2_hidden @ X23 @ X24 )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('44',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('48',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_ordinal1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('53',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( r1_ordinal1 @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('58',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_ordinal1 @ X19 )
      | ~ ( v3_ordinal1 @ X20 )
      | ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_ordinal1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('59',plain,
    ( ( ( r1_tarski @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( r1_tarski @ sk_A @ sk_B )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v3_ordinal1 @ X21 )
      | ( r2_hidden @ X22 @ X21 )
      | ( X22 = X21 )
      | ( r2_hidden @ X21 @ X22 )
      | ~ ( v3_ordinal1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( sk_B = sk_A )
      | ( r2_hidden @ sk_A @ sk_B ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('71',plain,
    ( ( ( sk_B = sk_A )
      | ~ ( r1_tarski @ sk_B @ sk_A ) )
   <= ( r1_ordinal1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B = sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('74',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) )
      & ( r1_ordinal1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X18: $i] :
      ( ( k1_ordinal1 @ X18 )
      = ( k2_xboole_0 @ X18 @ ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('76',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('77',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('78',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','79'])).

thf('81',plain,
    ( ~ ( r1_ordinal1 @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['74','80'])).

thf('82',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','39','40','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2P7aQQ1tB0
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:48:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 593 iterations in 0.268s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.50/0.73  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.50/0.73  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.50/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(t34_ordinal1, conjecture,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.73           ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.73             ( r1_ordinal1 @ A @ B ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i]:
% 0.50/0.73        ( ( v3_ordinal1 @ A ) =>
% 0.50/0.73          ( ![B:$i]:
% 0.50/0.73            ( ( v3_ordinal1 @ B ) =>
% 0.50/0.73              ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.50/0.73                ( r1_ordinal1 @ A @ B ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t34_ordinal1])).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)
% 0.50/0.73        | ~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.73       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.73      inference('split', [status(esa)], ['0'])).
% 0.50/0.73  thf(t26_ordinal1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.73           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (![X23 : $i, X24 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X23)
% 0.50/0.73          | (r1_ordinal1 @ X24 @ X23)
% 0.50/0.73          | (r2_hidden @ X23 @ X24)
% 0.50/0.73          | ~ (v3_ordinal1 @ X24))),
% 0.50/0.73      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.50/0.73  thf(l1_zfmisc_1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X15 : $i, X17 : $i]:
% 0.50/0.73         ((r1_tarski @ (k1_tarski @ X15) @ X17) | ~ (r2_hidden @ X15 @ X17))),
% 0.50/0.73      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.50/0.73  thf('4', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X0)
% 0.50/0.73          | (r1_ordinal1 @ X0 @ X1)
% 0.50/0.73          | ~ (v3_ordinal1 @ X1)
% 0.50/0.73          | (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['2', '3'])).
% 0.50/0.73  thf(t69_enumset1, axiom,
% 0.50/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.50/0.73  thf('5', plain, (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.73  thf(d2_tarski, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.50/0.73       ( ![D:$i]:
% 0.50/0.73         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.50/0.73         (((X9) != (X8))
% 0.50/0.73          | (r2_hidden @ X9 @ X10)
% 0.50/0.73          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d2_tarski])).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      (![X8 : $i, X11 : $i]: (r2_hidden @ X8 @ (k2_tarski @ X11 @ X8))),
% 0.50/0.73      inference('simplify', [status(thm)], ['6'])).
% 0.50/0.73  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['5', '7'])).
% 0.50/0.73  thf(t7_ordinal1, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      (![X25 : $i, X26 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.50/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.73  thf('10', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_tarski @ X0) @ X0)),
% 0.50/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.50/0.73  thf('11', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['4', '10'])).
% 0.50/0.73  thf('12', plain,
% 0.50/0.73      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.50/0.73      inference('simplify', [status(thm)], ['11'])).
% 0.50/0.73  thf('13', plain,
% 0.50/0.73      (((r1_ordinal1 @ sk_A @ sk_B) | (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('14', plain,
% 0.50/0.73      (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf(d1_ordinal1, axiom,
% 0.50/0.73    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.50/0.73  thf('15', plain,
% 0.50/0.73      (![X18 : $i]:
% 0.50/0.73         ((k1_ordinal1 @ X18) = (k2_xboole_0 @ X18 @ (k1_tarski @ X18)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.50/0.73  thf(d3_xboole_0, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i]:
% 0.50/0.73     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.50/0.73       ( ![D:$i]:
% 0.50/0.73         ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.73           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.50/0.73  thf('16', plain,
% 0.50/0.73      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X6 @ X4)
% 0.50/0.73          | (r2_hidden @ X6 @ X5)
% 0.50/0.73          | (r2_hidden @ X6 @ X3)
% 0.50/0.73          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.73  thf('17', plain,
% 0.50/0.73      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.50/0.73         ((r2_hidden @ X6 @ X3)
% 0.50/0.73          | (r2_hidden @ X6 @ X5)
% 0.50/0.73          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['16'])).
% 0.50/0.73  thf('18', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.50/0.73          | (r2_hidden @ X1 @ X0)
% 0.50/0.73          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['15', '17'])).
% 0.50/0.73  thf('19', plain,
% 0.50/0.73      ((((r2_hidden @ sk_A @ (k1_tarski @ sk_B)) | (r2_hidden @ sk_A @ sk_B)))
% 0.50/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['14', '18'])).
% 0.50/0.73  thf('20', plain,
% 0.50/0.73      (![X14 : $i]: ((k2_tarski @ X14 @ X14) = (k1_tarski @ X14))),
% 0.50/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.50/0.73  thf('21', plain,
% 0.50/0.73      (![X8 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X12 @ X10)
% 0.50/0.73          | ((X12) = (X11))
% 0.50/0.73          | ((X12) = (X8))
% 0.50/0.73          | ((X10) != (k2_tarski @ X11 @ X8)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d2_tarski])).
% 0.50/0.73  thf('22', plain,
% 0.50/0.73      (![X8 : $i, X11 : $i, X12 : $i]:
% 0.50/0.73         (((X12) = (X8))
% 0.50/0.73          | ((X12) = (X11))
% 0.50/0.73          | ~ (r2_hidden @ X12 @ (k2_tarski @ X11 @ X8)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['21'])).
% 0.50/0.73  thf('23', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['20', '22'])).
% 0.50/0.73  thf('24', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.50/0.73      inference('simplify', [status(thm)], ['23'])).
% 0.50/0.73  thf('25', plain,
% 0.50/0.73      ((((r2_hidden @ sk_A @ sk_B) | ((sk_A) = (sk_B))))
% 0.50/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['19', '24'])).
% 0.50/0.73  thf('26', plain,
% 0.50/0.73      (![X23 : $i, X24 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X23)
% 0.50/0.73          | (r1_ordinal1 @ X24 @ X23)
% 0.50/0.73          | (r2_hidden @ X23 @ X24)
% 0.50/0.73          | ~ (v3_ordinal1 @ X24))),
% 0.50/0.73      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.50/0.73  thf(antisymmetry_r2_hidden, axiom,
% 0.50/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.50/0.73  thf('27', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.50/0.73      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.50/0.73  thf('28', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X0)
% 0.50/0.73          | (r1_ordinal1 @ X0 @ X1)
% 0.50/0.73          | ~ (v3_ordinal1 @ X1)
% 0.50/0.73          | ~ (r2_hidden @ X0 @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['26', '27'])).
% 0.50/0.73  thf('29', plain,
% 0.50/0.73      (((((sk_A) = (sk_B))
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_B)
% 0.50/0.73         | (r1_ordinal1 @ sk_A @ sk_B)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_A)))
% 0.50/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['25', '28'])).
% 0.50/0.73  thf('30', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('31', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('32', plain,
% 0.50/0.73      (((((sk_A) = (sk_B)) | (r1_ordinal1 @ sk_A @ sk_B)))
% 0.50/0.73         <= (((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.50/0.73  thf('33', plain,
% 0.50/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('split', [status(esa)], ['0'])).
% 0.50/0.73  thf('34', plain,
% 0.50/0.73      ((((sk_A) = (sk_B)))
% 0.50/0.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['32', '33'])).
% 0.50/0.73  thf('35', plain,
% 0.50/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_B)) <= (~ ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('split', [status(esa)], ['0'])).
% 0.50/0.73  thf('36', plain,
% 0.50/0.73      ((~ (r1_ordinal1 @ sk_A @ sk_A))
% 0.50/0.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.50/0.73  thf('37', plain,
% 0.50/0.73      ((~ (v3_ordinal1 @ sk_A))
% 0.50/0.73         <= (~ ((r1_ordinal1 @ sk_A @ sk_B)) & 
% 0.50/0.73             ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['12', '36'])).
% 0.50/0.73  thf('38', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('39', plain,
% 0.50/0.73      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.73       ~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.73      inference('demod', [status(thm)], ['37', '38'])).
% 0.50/0.73  thf('40', plain,
% 0.50/0.73      (((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.73       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf('41', plain,
% 0.50/0.73      (![X18 : $i]:
% 0.50/0.73         ((k1_ordinal1 @ X18) = (k2_xboole_0 @ X18 @ (k1_tarski @ X18)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.50/0.73  thf('42', plain,
% 0.50/0.73      (![X23 : $i, X24 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X23)
% 0.50/0.73          | (r1_ordinal1 @ X24 @ X23)
% 0.50/0.73          | (r2_hidden @ X23 @ X24)
% 0.50/0.73          | ~ (v3_ordinal1 @ X24))),
% 0.50/0.73      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.50/0.73  thf('43', plain,
% 0.50/0.73      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X2 @ X5)
% 0.50/0.73          | (r2_hidden @ X2 @ X4)
% 0.50/0.73          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.73  thf('44', plain,
% 0.50/0.73      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.50/0.73         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.50/0.73      inference('simplify', [status(thm)], ['43'])).
% 0.50/0.73  thf('45', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X0)
% 0.50/0.73          | (r1_ordinal1 @ X0 @ X1)
% 0.50/0.73          | ~ (v3_ordinal1 @ X1)
% 0.50/0.73          | (r2_hidden @ X1 @ (k2_xboole_0 @ X0 @ X2)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['42', '44'])).
% 0.50/0.73  thf('46', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.50/0.73          | ~ (v3_ordinal1 @ X1)
% 0.50/0.73          | (r1_ordinal1 @ X0 @ X1)
% 0.50/0.73          | ~ (v3_ordinal1 @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['41', '45'])).
% 0.50/0.73  thf('47', plain,
% 0.50/0.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('split', [status(esa)], ['0'])).
% 0.50/0.73  thf('48', plain,
% 0.50/0.73      (((~ (v3_ordinal1 @ sk_B)
% 0.50/0.73         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_A)))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.50/0.73  thf('49', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('51', plain,
% 0.50/0.73      (((r1_ordinal1 @ sk_B @ sk_A))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.50/0.73  thf(redefinition_r1_ordinal1, axiom,
% 0.50/0.73    (![A:$i,B:$i]:
% 0.50/0.73     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.50/0.73       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.50/0.73  thf('52', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X19)
% 0.50/0.73          | ~ (v3_ordinal1 @ X20)
% 0.50/0.73          | (r1_tarski @ X19 @ X20)
% 0.50/0.73          | ~ (r1_ordinal1 @ X19 @ X20))),
% 0.50/0.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.73  thf('53', plain,
% 0.50/0.73      ((((r1_tarski @ sk_B @ sk_A)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_A)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_B)))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('sup-', [status(thm)], ['51', '52'])).
% 0.50/0.73  thf('54', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('55', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('56', plain,
% 0.50/0.73      (((r1_tarski @ sk_B @ sk_A))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.50/0.73  thf('57', plain,
% 0.50/0.73      (((r1_ordinal1 @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('split', [status(esa)], ['13'])).
% 0.50/0.73  thf('58', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X19)
% 0.50/0.73          | ~ (v3_ordinal1 @ X20)
% 0.50/0.73          | (r1_tarski @ X19 @ X20)
% 0.50/0.73          | ~ (r1_ordinal1 @ X19 @ X20))),
% 0.50/0.73      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.50/0.73  thf('59', plain,
% 0.50/0.73      ((((r1_tarski @ sk_A @ sk_B)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_B)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_A))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['57', '58'])).
% 0.50/0.73  thf('60', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('61', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('62', plain,
% 0.50/0.73      (((r1_tarski @ sk_A @ sk_B)) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.50/0.73  thf(t24_ordinal1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v3_ordinal1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( v3_ordinal1 @ B ) =>
% 0.50/0.73           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.50/0.73                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.50/0.73  thf('63', plain,
% 0.50/0.73      (![X21 : $i, X22 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X21)
% 0.50/0.73          | (r2_hidden @ X22 @ X21)
% 0.50/0.73          | ((X22) = (X21))
% 0.50/0.73          | (r2_hidden @ X21 @ X22)
% 0.50/0.73          | ~ (v3_ordinal1 @ X22))),
% 0.50/0.73      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.50/0.73  thf('64', plain,
% 0.50/0.73      (![X25 : $i, X26 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.50/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.73  thf('65', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (~ (v3_ordinal1 @ X1)
% 0.50/0.73          | (r2_hidden @ X0 @ X1)
% 0.50/0.73          | ((X1) = (X0))
% 0.50/0.73          | ~ (v3_ordinal1 @ X0)
% 0.50/0.73          | ~ (r1_tarski @ X0 @ X1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.50/0.73  thf('66', plain,
% 0.50/0.73      (((~ (v3_ordinal1 @ sk_A)
% 0.50/0.73         | ((sk_B) = (sk_A))
% 0.50/0.73         | (r2_hidden @ sk_A @ sk_B)
% 0.50/0.73         | ~ (v3_ordinal1 @ sk_B))) <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['62', '65'])).
% 0.50/0.73  thf('67', plain, ((v3_ordinal1 @ sk_A)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('68', plain, ((v3_ordinal1 @ sk_B)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('69', plain,
% 0.50/0.73      (((((sk_B) = (sk_A)) | (r2_hidden @ sk_A @ sk_B)))
% 0.50/0.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.50/0.73  thf('70', plain,
% 0.50/0.73      (![X25 : $i, X26 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.50/0.73      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.73  thf('71', plain,
% 0.50/0.73      (((((sk_B) = (sk_A)) | ~ (r1_tarski @ sk_B @ sk_A)))
% 0.50/0.73         <= (((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['69', '70'])).
% 0.50/0.73  thf('72', plain,
% 0.50/0.73      ((((sk_B) = (sk_A)))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.50/0.73             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['56', '71'])).
% 0.50/0.73  thf('73', plain,
% 0.50/0.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))))),
% 0.50/0.73      inference('split', [status(esa)], ['0'])).
% 0.50/0.73  thf('74', plain,
% 0.50/0.73      ((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A)))
% 0.50/0.73         <= (~ ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B))) & 
% 0.50/0.73             ((r1_ordinal1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['72', '73'])).
% 0.50/0.73  thf('75', plain,
% 0.50/0.73      (![X18 : $i]:
% 0.50/0.73         ((k1_ordinal1 @ X18) = (k2_xboole_0 @ X18 @ (k1_tarski @ X18)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.50/0.73  thf('76', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['5', '7'])).
% 0.50/0.73  thf('77', plain,
% 0.50/0.73      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.73         (~ (r2_hidden @ X2 @ X3)
% 0.50/0.73          | (r2_hidden @ X2 @ X4)
% 0.50/0.73          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.50/0.73      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.50/0.73  thf('78', plain,
% 0.50/0.73      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.50/0.73         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.50/0.73      inference('simplify', [status(thm)], ['77'])).
% 0.50/0.73  thf('79', plain,
% 0.50/0.73      (![X0 : $i, X1 : $i]:
% 0.50/0.73         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.50/0.73      inference('sup-', [status(thm)], ['76', '78'])).
% 0.50/0.73  thf('80', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_ordinal1 @ X0))),
% 0.50/0.73      inference('sup+', [status(thm)], ['75', '79'])).
% 0.50/0.73  thf('81', plain,
% 0.50/0.73      (~ ((r1_ordinal1 @ sk_A @ sk_B)) | 
% 0.50/0.73       ((r2_hidden @ sk_A @ (k1_ordinal1 @ sk_B)))),
% 0.50/0.73      inference('demod', [status(thm)], ['74', '80'])).
% 0.50/0.73  thf('82', plain, ($false),
% 0.50/0.73      inference('sat_resolution*', [status(thm)], ['1', '39', '40', '81'])).
% 0.50/0.73  
% 0.50/0.73  % SZS output end Refutation
% 0.50/0.73  
% 0.50/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
