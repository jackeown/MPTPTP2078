%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mNt6FC3OQT

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:55 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  139 (1798 expanded)
%              Number of leaves         :   20 ( 520 expanded)
%              Depth                    :   36
%              Number of atoms          : 1000 (15620 expanded)
%              Number of equality atoms :   37 ( 331 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('1',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
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

thf(t33_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
          <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r2_hidden @ A @ B )
            <=> ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_ordinal1])).

thf('8',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_ordinal1 @ X17 )
      | ( r1_ordinal1 @ X18 @ X17 )
      | ( r2_hidden @ X17 @ X18 )
      | ~ ( v3_ordinal1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('13',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['8'])).

thf('14',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( r1_ordinal1 @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r1_ordinal1 @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(redefinition_r1_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_ordinal1 @ A )
        & ( v3_ordinal1 @ B ) )
     => ( ( r1_ordinal1 @ A @ B )
      <=> ( r1_tarski @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('19',plain,
    ( ( ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t24_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_hidden @ A @ B )
              & ( A != B )
              & ~ ( r2_hidden @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ X15 @ X16 )
      | ~ ( v3_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t24_ordinal1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ~ ( v3_ordinal1 @ sk_B )
      | ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A )
      | ~ ( v3_ordinal1 @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( sk_A = sk_B )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( sk_A = sk_B )
        | ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_A = sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['11','32'])).

thf(t29_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ) )).

thf('34',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('35',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('36',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('39',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ ( k1_ordinal1 @ sk_A ) @ sk_B )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('46',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ~ ( v3_ordinal1 @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ~ ( v3_ordinal1 @ sk_A )
      | ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','48'])).

thf('50',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( ( r2_hidden @ ( k1_ordinal1 @ sk_A ) @ sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('53',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( sk_A = sk_B )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','53'])).

thf(t10_ordinal1,axiom,(
    ! [A: $i] :
      ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ) )).

thf('55',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('57',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_A = sk_B ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('60',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( sk_B
        = ( k1_ordinal1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) ) )
   <= ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('62',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_ordinal1 @ sk_A ) )
      | ( sk_B
        = ( k1_ordinal1 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i] :
      ( r2_hidden @ X14 @ ( k1_ordinal1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t10_ordinal1])).

thf('64',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('65',plain,
    ( ( sk_A
      = ( k1_ordinal1 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r1_tarski @ ( k1_ordinal1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = sk_B )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('69',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('70',plain,
    ( ( r1_tarski @ sk_A @ sk_A )
   <= ( ~ ( r2_hidden @ sk_A @ sk_B )
      & ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['10','71'])).

thf('73',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['9','72'])).

thf('74',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('75',plain,(
    ! [X19: $i] :
      ( ( v3_ordinal1 @ ( k1_ordinal1 @ X19 ) )
      | ~ ( v3_ordinal1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t29_ordinal1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_ordinal1 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('77',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v3_ordinal1 @ X12 )
      | ~ ( v3_ordinal1 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_ordinal1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_ordinal1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( r1_ordinal1 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ~ ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['9','72'])).

thf('81',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    r1_tarski @ sk_B @ ( k1_ordinal1 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('88',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_ordinal1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['74','90'])).

thf('92',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( r2_hidden @ sk_B @ ( k1_ordinal1 @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X11: $i] :
      ( ( k1_ordinal1 @ X11 )
      = ( k2_xboole_0 @ X11 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('95',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('96',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','96'])).

thf('98',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('101',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( r1_ordinal1 @ ( k1_ordinal1 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf('103',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['10','71','102'])).

thf('104',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['101','103'])).

thf('105',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_ordinal1 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['98','104'])).

thf('106',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( r1_tarski @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('107',plain,
    ( ( ( k1_ordinal1 @ sk_A )
      = sk_B )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['36'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('109',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X8 ) @ X10 )
      | ~ ( r2_hidden @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('110',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['10','71','102'])).

thf('112',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(simpl_trail,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_B ),
    inference(demod,[status(thm)],['107','112'])).

thf('114',plain,(
    ~ ( r1_ordinal1 @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['73','113'])).

thf('115',plain,(
    ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','114'])).

thf('116',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['115','116'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mNt6FC3OQT
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:11:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.49/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.69  % Solved by: fo/fo7.sh
% 0.49/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.69  % done 572 iterations in 0.233s
% 0.49/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.69  % SZS output start Refutation
% 0.49/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.69  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.49/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.69  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.49/0.69  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.49/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.69  thf(t26_ordinal1, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.69           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.49/0.69  thf('0', plain,
% 0.49/0.69      (![X17 : $i, X18 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X17)
% 0.49/0.69          | (r1_ordinal1 @ X18 @ X17)
% 0.49/0.69          | (r2_hidden @ X17 @ X18)
% 0.49/0.69          | ~ (v3_ordinal1 @ X18))),
% 0.49/0.69      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.49/0.69  thf('1', plain,
% 0.49/0.69      (![X17 : $i, X18 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X17)
% 0.49/0.69          | (r1_ordinal1 @ X18 @ X17)
% 0.49/0.69          | (r2_hidden @ X17 @ X18)
% 0.49/0.69          | ~ (v3_ordinal1 @ X18))),
% 0.49/0.69      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.49/0.69  thf(antisymmetry_r2_hidden, axiom,
% 0.49/0.69    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.49/0.69  thf('2', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.69      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.49/0.69  thf('3', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X0)
% 0.49/0.69          | (r1_ordinal1 @ X0 @ X1)
% 0.49/0.69          | ~ (v3_ordinal1 @ X1)
% 0.49/0.69          | ~ (r2_hidden @ X0 @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.69  thf('4', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X0)
% 0.49/0.69          | (r1_ordinal1 @ X0 @ X1)
% 0.49/0.69          | ~ (v3_ordinal1 @ X1)
% 0.49/0.69          | ~ (v3_ordinal1 @ X0)
% 0.49/0.69          | (r1_ordinal1 @ X1 @ X0)
% 0.49/0.69          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['0', '3'])).
% 0.49/0.69  thf('5', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]:
% 0.49/0.69         ((r1_ordinal1 @ X1 @ X0)
% 0.49/0.69          | ~ (v3_ordinal1 @ X1)
% 0.49/0.69          | (r1_ordinal1 @ X0 @ X1)
% 0.49/0.69          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['4'])).
% 0.49/0.69  thf('6', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X0) | (r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.49/0.69      inference('eq_fact', [status(thm)], ['5'])).
% 0.49/0.69  thf('7', plain,
% 0.49/0.69      (![X0 : $i]: ((r1_ordinal1 @ X0 @ X0) | ~ (v3_ordinal1 @ X0))),
% 0.49/0.69      inference('simplify', [status(thm)], ['6'])).
% 0.49/0.69  thf(t33_ordinal1, conjecture,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.69       ( ![B:$i]:
% 0.49/0.69         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.69           ( ( r2_hidden @ A @ B ) <=>
% 0.49/0.69             ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.69    (~( ![A:$i]:
% 0.49/0.69        ( ( v3_ordinal1 @ A ) =>
% 0.49/0.69          ( ![B:$i]:
% 0.49/0.69            ( ( v3_ordinal1 @ B ) =>
% 0.49/0.69              ( ( r2_hidden @ A @ B ) <=>
% 0.49/0.69                ( r1_ordinal1 @ ( k1_ordinal1 @ A ) @ B ) ) ) ) ) )),
% 0.49/0.69    inference('cnf.neg', [status(esa)], [t33_ordinal1])).
% 0.49/0.69  thf('8', plain,
% 0.49/0.69      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.49/0.69        | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('9', plain,
% 0.49/0.69      ((~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.49/0.69         <= (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.69      inference('split', [status(esa)], ['8'])).
% 0.49/0.69  thf('10', plain,
% 0.49/0.69      (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)) | 
% 0.49/0.69       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.49/0.69      inference('split', [status(esa)], ['8'])).
% 0.49/0.69  thf(d1_ordinal1, axiom,
% 0.49/0.69    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.49/0.69  thf('11', plain,
% 0.49/0.69      (![X11 : $i]:
% 0.49/0.69         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.49/0.69  thf('12', plain,
% 0.49/0.69      (![X17 : $i, X18 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X17)
% 0.49/0.69          | (r1_ordinal1 @ X18 @ X17)
% 0.49/0.69          | (r2_hidden @ X17 @ X18)
% 0.49/0.69          | ~ (v3_ordinal1 @ X18))),
% 0.49/0.69      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.49/0.69  thf('13', plain,
% 0.49/0.69      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('split', [status(esa)], ['8'])).
% 0.49/0.69  thf('14', plain,
% 0.49/0.69      (((~ (v3_ordinal1 @ sk_B)
% 0.49/0.69         | (r1_ordinal1 @ sk_B @ sk_A)
% 0.49/0.69         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.69  thf('15', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('16', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('17', plain,
% 0.49/0.69      (((r1_ordinal1 @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.69      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.49/0.69  thf(redefinition_r1_ordinal1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( ( v3_ordinal1 @ A ) & ( v3_ordinal1 @ B ) ) =>
% 0.49/0.69       ( ( r1_ordinal1 @ A @ B ) <=> ( r1_tarski @ A @ B ) ) ))).
% 0.49/0.69  thf('18', plain,
% 0.49/0.69      (![X12 : $i, X13 : $i]:
% 0.49/0.69         (~ (v3_ordinal1 @ X12)
% 0.49/0.70          | ~ (v3_ordinal1 @ X13)
% 0.49/0.70          | (r1_tarski @ X12 @ X13)
% 0.49/0.70          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      ((((r1_tarski @ sk_B @ sk_A)
% 0.49/0.70         | ~ (v3_ordinal1 @ sk_A)
% 0.49/0.70         | ~ (v3_ordinal1 @ sk_B))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.70  thf('20', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('21', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.70  thf(t24_ordinal1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v3_ordinal1 @ A ) =>
% 0.49/0.70       ( ![B:$i]:
% 0.49/0.70         ( ( v3_ordinal1 @ B ) =>
% 0.49/0.70           ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.49/0.70                ( ~( r2_hidden @ B @ A ) ) ) ) ) ) ))).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (![X15 : $i, X16 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X15)
% 0.49/0.70          | (r2_hidden @ X16 @ X15)
% 0.49/0.70          | ((X16) = (X15))
% 0.49/0.70          | (r2_hidden @ X15 @ X16)
% 0.49/0.70          | ~ (v3_ordinal1 @ X16))),
% 0.49/0.70      inference('cnf', [status(esa)], [t24_ordinal1])).
% 0.49/0.70  thf(t7_ordinal1, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      (![X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.70  thf('25', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X1)
% 0.49/0.70          | (r2_hidden @ X0 @ X1)
% 0.49/0.70          | ((X1) = (X0))
% 0.49/0.70          | ~ (v3_ordinal1 @ X0)
% 0.49/0.70          | ~ (r1_tarski @ X0 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (((~ (v3_ordinal1 @ sk_B)
% 0.49/0.70         | ((sk_A) = (sk_B))
% 0.49/0.70         | (r2_hidden @ sk_B @ sk_A)
% 0.49/0.70         | ~ (v3_ordinal1 @ sk_A))) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['22', '25'])).
% 0.49/0.70  thf('27', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('28', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (((((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ sk_A)))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.49/0.70  thf(d3_xboole_0, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.49/0.70       ( ![D:$i]:
% 0.49/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.70           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.49/0.70  thf('30', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X2 @ X5)
% 0.49/0.70          | (r2_hidden @ X2 @ X4)
% 0.49/0.70          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.49/0.70         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.49/0.70      inference('simplify', [status(thm)], ['30'])).
% 0.49/0.70  thf('32', plain,
% 0.49/0.70      ((![X0 : $i]:
% 0.49/0.70          (((sk_A) = (sk_B)) | (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_A @ X0))))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['29', '31'])).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      ((((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A)) | ((sk_A) = (sk_B))))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup+', [status(thm)], ['11', '32'])).
% 0.49/0.70  thf(t29_ordinal1, axiom,
% 0.49/0.70    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v3_ordinal1 @ ( k1_ordinal1 @ A ) ) ))).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X19 : $i]:
% 0.49/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.49/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      (![X19 : $i]:
% 0.49/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.49/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.49/0.70  thf('36', plain,
% 0.49/0.70      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('37', plain,
% 0.49/0.70      (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('split', [status(esa)], ['36'])).
% 0.49/0.70  thf('38', plain,
% 0.49/0.70      (![X12 : $i, X13 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X12)
% 0.49/0.70          | ~ (v3_ordinal1 @ X13)
% 0.49/0.70          | (r1_tarski @ X12 @ X13)
% 0.49/0.70          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.49/0.70  thf('39', plain,
% 0.49/0.70      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.49/0.70         | ~ (v3_ordinal1 @ sk_B)
% 0.49/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.70  thf('40', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('41', plain,
% 0.49/0.70      ((((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.49/0.70         | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['39', '40'])).
% 0.49/0.70  thf('42', plain,
% 0.49/0.70      (((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['35', '41'])).
% 0.49/0.70  thf('43', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('44', plain,
% 0.49/0.70      (((r1_tarski @ (k1_ordinal1 @ sk_A) @ sk_B))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['42', '43'])).
% 0.49/0.70  thf('45', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X1)
% 0.49/0.70          | (r2_hidden @ X0 @ X1)
% 0.49/0.70          | ((X1) = (X0))
% 0.49/0.70          | ~ (v3_ordinal1 @ X0)
% 0.49/0.70          | ~ (r1_tarski @ X0 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.49/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 0.49/0.70         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.49/0.70         | ~ (v3_ordinal1 @ sk_B)))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.70  thf('47', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('48', plain,
% 0.49/0.70      (((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.49/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))
% 0.49/0.70         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['46', '47'])).
% 0.49/0.70  thf('49', plain,
% 0.49/0.70      (((~ (v3_ordinal1 @ sk_A)
% 0.49/0.70         | (r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.49/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['34', '48'])).
% 0.49/0.70  thf('50', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('51', plain,
% 0.49/0.70      ((((r2_hidden @ (k1_ordinal1 @ sk_A) @ sk_B)
% 0.49/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['49', '50'])).
% 0.49/0.70  thf('52', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.70      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.49/0.70  thf('53', plain,
% 0.49/0.70      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.49/0.70         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.49/0.70  thf('54', plain,
% 0.49/0.70      (((((sk_A) = (sk_B)) | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '53'])).
% 0.49/0.70  thf(t10_ordinal1, axiom, (![A:$i]: ( r2_hidden @ A @ ( k1_ordinal1 @ A ) ))).
% 0.49/0.70  thf('55', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.49/0.70  thf('56', plain,
% 0.49/0.70      (![X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.70  thf('57', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.49/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.70  thf('58', plain,
% 0.49/0.70      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_A) = (sk_B))))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['54', '57'])).
% 0.49/0.70  thf('59', plain,
% 0.49/0.70      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.70  thf('60', plain,
% 0.49/0.70      ((((sk_A) = (sk_B)))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.70  thf('61', plain,
% 0.49/0.70      (((((sk_B) = (k1_ordinal1 @ sk_A))
% 0.49/0.70         | ~ (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.49/0.70  thf('62', plain,
% 0.49/0.70      (((~ (r2_hidden @ sk_A @ (k1_ordinal1 @ sk_A))
% 0.49/0.70         | ((sk_B) = (k1_ordinal1 @ sk_A))))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.49/0.70  thf('63', plain, (![X14 : $i]: (r2_hidden @ X14 @ (k1_ordinal1 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [t10_ordinal1])).
% 0.49/0.70  thf('64', plain,
% 0.49/0.70      ((((sk_A) = (sk_B)))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.70  thf('65', plain,
% 0.49/0.70      ((((sk_A) = (k1_ordinal1 @ sk_A)))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.49/0.70  thf('66', plain, (![X0 : $i]: ~ (r1_tarski @ (k1_ordinal1 @ X0) @ X0)),
% 0.49/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.70  thf('67', plain,
% 0.49/0.70      ((~ (r1_tarski @ sk_A @ sk_A))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.70  thf('68', plain,
% 0.49/0.70      ((((sk_A) = (sk_B)))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['58', '59'])).
% 0.49/0.70  thf('69', plain,
% 0.49/0.70      (((r1_tarski @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.49/0.70  thf('70', plain,
% 0.49/0.70      (((r1_tarski @ sk_A @ sk_A))
% 0.49/0.70         <= (~ ((r2_hidden @ sk_A @ sk_B)) & 
% 0.49/0.70             ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('sup+', [status(thm)], ['68', '69'])).
% 0.49/0.70  thf('71', plain,
% 0.49/0.70      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.49/0.70       ~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['67', '70'])).
% 0.49/0.70  thf('72', plain, (~ ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.49/0.70      inference('sat_resolution*', [status(thm)], ['10', '71'])).
% 0.49/0.70  thf('73', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['9', '72'])).
% 0.49/0.70  thf('74', plain,
% 0.49/0.70      (![X19 : $i]:
% 0.49/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.49/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.49/0.70  thf('75', plain,
% 0.49/0.70      (![X19 : $i]:
% 0.49/0.70         ((v3_ordinal1 @ (k1_ordinal1 @ X19)) | ~ (v3_ordinal1 @ X19))),
% 0.49/0.70      inference('cnf', [status(esa)], [t29_ordinal1])).
% 0.49/0.70  thf('76', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_ordinal1 @ X1 @ X0)
% 0.49/0.70          | ~ (v3_ordinal1 @ X1)
% 0.49/0.70          | (r1_ordinal1 @ X0 @ X1)
% 0.49/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['4'])).
% 0.49/0.70  thf('77', plain,
% 0.49/0.70      (![X12 : $i, X13 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X12)
% 0.49/0.70          | ~ (v3_ordinal1 @ X13)
% 0.49/0.70          | (r1_tarski @ X12 @ X13)
% 0.49/0.70          | ~ (r1_ordinal1 @ X12 @ X13))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_r1_ordinal1])).
% 0.49/0.70  thf('78', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X0)
% 0.49/0.70          | (r1_ordinal1 @ X0 @ X1)
% 0.49/0.70          | ~ (v3_ordinal1 @ X1)
% 0.49/0.70          | (r1_tarski @ X1 @ X0)
% 0.49/0.70          | ~ (v3_ordinal1 @ X0)
% 0.49/0.70          | ~ (v3_ordinal1 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['76', '77'])).
% 0.49/0.70  thf('79', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         ((r1_tarski @ X1 @ X0)
% 0.49/0.70          | ~ (v3_ordinal1 @ X1)
% 0.49/0.70          | (r1_ordinal1 @ X0 @ X1)
% 0.49/0.70          | ~ (v3_ordinal1 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['78'])).
% 0.49/0.70  thf('80', plain, (~ (r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B)),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['9', '72'])).
% 0.49/0.70  thf('81', plain,
% 0.49/0.70      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.49/0.70        | ~ (v3_ordinal1 @ sk_B)
% 0.49/0.70        | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['79', '80'])).
% 0.49/0.70  thf('82', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('83', plain,
% 0.49/0.70      ((~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A))
% 0.49/0.70        | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['81', '82'])).
% 0.49/0.70  thf('84', plain,
% 0.49/0.70      ((~ (v3_ordinal1 @ sk_A) | (r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['75', '83'])).
% 0.49/0.70  thf('85', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('86', plain, ((r1_tarski @ sk_B @ (k1_ordinal1 @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['84', '85'])).
% 0.49/0.70  thf('87', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (v3_ordinal1 @ X1)
% 0.49/0.70          | (r2_hidden @ X0 @ X1)
% 0.49/0.70          | ((X1) = (X0))
% 0.49/0.70          | ~ (v3_ordinal1 @ X0)
% 0.49/0.70          | ~ (r1_tarski @ X0 @ X1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.70  thf('88', plain,
% 0.49/0.70      ((~ (v3_ordinal1 @ sk_B)
% 0.49/0.70        | ((k1_ordinal1 @ sk_A) = (sk_B))
% 0.49/0.70        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.49/0.70        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['86', '87'])).
% 0.49/0.70  thf('89', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('90', plain,
% 0.49/0.70      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.49/0.70        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.49/0.70        | ~ (v3_ordinal1 @ (k1_ordinal1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['88', '89'])).
% 0.49/0.70  thf('91', plain,
% 0.49/0.70      ((~ (v3_ordinal1 @ sk_A)
% 0.49/0.70        | (r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.49/0.70        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['74', '90'])).
% 0.49/0.70  thf('92', plain, ((v3_ordinal1 @ sk_A)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('93', plain,
% 0.49/0.70      (((r2_hidden @ sk_B @ (k1_ordinal1 @ sk_A))
% 0.49/0.70        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['91', '92'])).
% 0.49/0.70  thf('94', plain,
% 0.49/0.70      (![X11 : $i]:
% 0.49/0.70         ((k1_ordinal1 @ X11) = (k2_xboole_0 @ X11 @ (k1_tarski @ X11)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.49/0.70  thf('95', plain,
% 0.49/0.70      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X6 @ X4)
% 0.49/0.70          | (r2_hidden @ X6 @ X5)
% 0.49/0.70          | (r2_hidden @ X6 @ X3)
% 0.49/0.70          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.49/0.70  thf('96', plain,
% 0.49/0.70      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.49/0.70         ((r2_hidden @ X6 @ X3)
% 0.49/0.70          | (r2_hidden @ X6 @ X5)
% 0.49/0.70          | ~ (r2_hidden @ X6 @ (k2_xboole_0 @ X5 @ X3)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['95'])).
% 0.49/0.70  thf('97', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.49/0.70          | (r2_hidden @ X1 @ X0)
% 0.49/0.70          | (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['94', '96'])).
% 0.49/0.70  thf('98', plain,
% 0.49/0.70      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.49/0.70        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.70        | (r2_hidden @ sk_B @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['93', '97'])).
% 0.49/0.70  thf('99', plain,
% 0.49/0.70      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('split', [status(esa)], ['36'])).
% 0.49/0.70  thf('100', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.70      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.49/0.70  thf('101', plain,
% 0.49/0.70      ((~ (r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['99', '100'])).
% 0.49/0.70  thf('102', plain,
% 0.49/0.70      (((r2_hidden @ sk_A @ sk_B)) | 
% 0.49/0.70       ((r1_ordinal1 @ (k1_ordinal1 @ sk_A) @ sk_B))),
% 0.49/0.70      inference('split', [status(esa)], ['36'])).
% 0.49/0.70  thf('103', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.49/0.70      inference('sat_resolution*', [status(thm)], ['10', '71', '102'])).
% 0.49/0.70  thf('104', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['101', '103'])).
% 0.49/0.70  thf('105', plain,
% 0.49/0.70      (((r2_hidden @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.70        | ((k1_ordinal1 @ sk_A) = (sk_B)))),
% 0.49/0.70      inference('clc', [status(thm)], ['98', '104'])).
% 0.49/0.70  thf('106', plain,
% 0.49/0.70      (![X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X20 @ X21) | ~ (r1_tarski @ X21 @ X20))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.70  thf('107', plain,
% 0.49/0.70      ((((k1_ordinal1 @ sk_A) = (sk_B))
% 0.49/0.70        | ~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B))),
% 0.49/0.70      inference('sup-', [status(thm)], ['105', '106'])).
% 0.49/0.70  thf('108', plain,
% 0.49/0.70      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('split', [status(esa)], ['36'])).
% 0.49/0.70  thf(l1_zfmisc_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.49/0.70  thf('109', plain,
% 0.49/0.70      (![X8 : $i, X10 : $i]:
% 0.49/0.70         ((r1_tarski @ (k1_tarski @ X8) @ X10) | ~ (r2_hidden @ X8 @ X10))),
% 0.49/0.70      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.49/0.70  thf('110', plain,
% 0.49/0.70      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.49/0.70         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['108', '109'])).
% 0.49/0.70  thf('111', plain, (((r2_hidden @ sk_A @ sk_B))),
% 0.49/0.70      inference('sat_resolution*', [status(thm)], ['10', '71', '102'])).
% 0.49/0.70  thf('112', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.49/0.70      inference('simpl_trail', [status(thm)], ['110', '111'])).
% 0.49/0.70  thf('113', plain, (((k1_ordinal1 @ sk_A) = (sk_B))),
% 0.49/0.70      inference('demod', [status(thm)], ['107', '112'])).
% 0.49/0.70  thf('114', plain, (~ (r1_ordinal1 @ sk_B @ sk_B)),
% 0.49/0.70      inference('demod', [status(thm)], ['73', '113'])).
% 0.49/0.70  thf('115', plain, (~ (v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('sup-', [status(thm)], ['7', '114'])).
% 0.49/0.70  thf('116', plain, ((v3_ordinal1 @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('117', plain, ($false), inference('demod', [status(thm)], ['115', '116'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
